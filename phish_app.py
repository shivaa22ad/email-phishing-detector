#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import email
import ipaddress
import io
import json
import quopri
import re
from html.parser import HTMLParser
from typing import List, Tuple, Dict, Optional
from urllib.parse import urlparse

import streamlit as st

# Optional dependency: tldextract (kept offline by disabling suffix list fetch)
try:
    import tldextract
    _EXTRACTOR = tldextract.TLDExtract(suffix_list_urls=None)
except Exception:
    _EXTRACTOR = None

# ----------------------------
# Config (tune for your needs)
# ----------------------------
WHITELIST_DOMAINS = {
    "gmail.com", "outlook.com", "yahoo.com",
    "google.com", "google.co.in", "microsoft.com", "office.com",
    "amazon.in", "amazon.com", "apple.com", "icloud.com",
    "github.com", "paypal.com", "netflix.com"
}

BRAND_DOMAINS = {
    "google": {"google.com", "google.co.in"},
    "microsoft": {"microsoft.com", "office.com", "live.com"},
    "paypal": {"paypal.com"},
    "amazon": {"amazon.com", "amazon.in"},
    "apple": {"apple.com", "icloud.com"},
    "github": {"github.com"},
    "netflix": {"netflix.com"},
}

URL_SHORTENERS = {
    "bit.ly", "tinyurl.com", "t.co", "goo.gl", "ow.ly", "is.gd", "buff.ly",
    "rebrand.ly", "cutt.ly", "t.ly", "s.id", "rb.gy"
}

SUSPICIOUS_EXTENSIONS = {
    ".exe", ".scr", ".js", ".vbs", ".bat", ".cmd", ".jar", ".ps1",
    ".docm", ".xlsm", ".pptm", ".msi", ".apk", ".iso", ".img"
}

URGENCY_WORDS = re.compile(
    r"\b(urgent|immediate|verify|suspend|expired|account locked|confirm now|"
    r"click now|reset password|unauthorized|security alert|limited time)\b",
    re.I
)


# ----------------------------
# Utilities
# ----------------------------
def safe_decode(s: Optional[str]) -> str:
    if not s:
        return ""
    from email.header import decode_header, make_header
    try:
        return str(make_header(decode_header(s)))
    except Exception:
        return s

def extract_registered_domain(host: str) -> str:
    host = (host or "").strip().lower()
    if not host:
        return host
    try:
        ipaddress.ip_address(host)
        return host
    except Exception:
        pass
    if _EXTRACTOR:
        ext = _EXTRACTOR(host)
        if ext.domain and ext.suffix:
            return f"{ext.domain}.{ext.suffix}"
        return host
    parts = host.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else host

def is_ip_host(host: str) -> bool:
    try:
        ipaddress.ip_address(host)
        return True
    except Exception:
        return False

def looks_punycode(host: str) -> bool:
    return "xn--" in (host or "")

def has_non_ascii(s: str) -> bool:
    try:
        (s or "").encode("ascii")
        return False
    except Exception:
        return True

def levenshtein(a: str, b: str) -> int:
    a, b = (a or "").lower(), (b or "").lower()
    if a == b: return 0
    if not a: return len(b)
    if not b: return len(a)
    dp = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        prev = i
        for j, cb in enumerate(b, 1):
            cost = 0 if ca == cb else 1
            cur = min(dp[j] + 1, prev + 1, dp[j-1] + cost)
            dp[j-1] = prev
            prev = cur
        dp[-1] = prev
    return dp[-1]


# ----------------------------
# HTML helpers
# ----------------------------
class LinkExtractor(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links: List[Tuple[str, str]] = []
        self._in_a = False
        self._txt = []
        self._href = None

    def handle_starttag(self, tag, attrs):
        if tag.lower() == "a":
            self._in_a = True
            self._href = dict(attrs).get("href", "")

    def handle_endtag(self, tag):
        if tag.lower() == "a" and self._in_a:
            text = "".join(self._txt).strip()
            self.links.append((text, self._href or ""))
            self._in_a = False
            self._txt, self._href = [], None

    def handle_data(self, data):
        if self._in_a:
            self._txt.append(data)

def extract_links_from_html(html: str) -> List[Tuple[str, str]]:
    parser = LinkExtractor()
    try:
        parser.feed(html or "")
    except Exception:
        pass
    return parser.links


# ----------------------------
# Email parsing
# ----------------------------
def _decode_bytes(b: bytes, charset: Optional[str]) -> str:
    if not b: return ""
    if charset:
        try:
            return b.decode(charset, "ignore")
        except Exception:
            pass
    try:
        return quopri.decodestring(b).decode("utf-8", "ignore")
    except Exception:
        return b.decode("utf-8", "ignore")

def get_body_parts(msg) -> Tuple[str, str]:
    text_parts, html_parts = [], []
    if msg.is_multipart():
        for part in msg.walk():
            ctype = part.get_content_type()
            disp = (part.get("Content-Disposition") or "").lower()
            if ctype == "text/plain" and "attachment" not in disp:
                text_parts.append(_decode_bytes(part.get_payload(decode=True) or b"", part.get_content_charset()))
            elif ctype == "text/html" and "attachment" not in disp:
                html_parts.append(_decode_bytes(part.get_payload(decode=True) or b"", part.get_content_charset()))
    else:
        ctype = msg.get_content_type()
        payload = msg.get_payload(decode=True) or b""
        if ctype == "text/plain":
            text_parts.append(_decode_bytes(payload, msg.get_content_charset()))
        elif ctype == "text/html":
            html_parts.append(_decode_bytes(payload, msg.get_content_charset()))
        else:
            try: text_parts.append(payload.decode("utf-8", "ignore"))
            except Exception: text_parts.append(payload.decode("latin-1", "ignore"))
    return ("\n".join(text_parts).strip(), "\n".join(html_parts).strip())

def get_attachments(msg) -> List[str]:
    names = []
    for part in msg.walk():
        disp = (part.get("Content-Disposition") or "").lower()
        if "attachment" in disp:
            names.append(safe_decode(part.get_filename() or "(no-name)"))
    return names


# ----------------------------
# Heuristics
# ----------------------------
def check_headers(msg) -> Tuple[int, List[str]]:
    points, reasons = 0, []
    subj = safe_decode(msg.get("Subject", ""))
    from_name, from_email = email.utils.parseaddr(msg.get("From", ""))
    reply_to = email.utils.parseaddr(msg.get("Reply-To", ""))[1] or ""
    return_path = email.utils.parseaddr(msg.get("Return-Path", ""))[1] or ""
    auth_results = (msg.get("Authentication-Results") or "").lower()

    from_domain = (from_email.split("@")[-1] or "").lower()
    reply_domain = (reply_to.split("@")[-1] or "").lower()
    return_domain = (return_path.split("@")[-1] or "").lower()

    if reply_to and reply_domain and reply_domain != from_domain:
        points += 15; reasons.append(f"Reply-To domain differs from From: {reply_domain} ≠ {from_domain}")
    if return_path and return_domain and return_domain != from_domain:
        points += 10; reasons.append(f"Return-Path domain differs from From: {return_domain} ≠ {from_domain}")

    if "spf=fail" in auth_results or "spf=softfail" in auth_results:
        points += 15; reasons.append("SPF failed (per Authentication-Results)")
    if "dkim=fail" in auth_results or "dkim=none" in auth_results:
        points += 15; reasons.append("DKIM failed/none (per Authentication-Results)")
    if "dmarc=fail" in auth_results:
        points += 20; reasons.append("DMARC fail (per Authentication-Results)")

    disp = (from_name or "").lower()
    reg = extract_registered_domain(from_domain)
    for brand, legit_domains in BRAND_DOMAINS.items():
        if brand in disp and reg not in legit_domains:
            points += 20; reasons.append(f"Display name '{from_name}' mentions '{brand}' but domain is {reg}, not legit")

    if URGENCY_WORDS.search(subj):
        points += 8; reasons.append("Urgent/pressure wording in Subject")

    if reg and reg not in WHITELIST_DOMAINS:
        points += 5; reasons.append(f"Sender domain not in whitelist: {reg}")
    return points, reasons

def check_body(text: str, html: str, subject: str) -> Tuple[int, List[str], List[Tuple[str, str]]]:
    points, reasons = 0, []
    links: List[Tuple[str, str]] = []
    content = f"{subject}\n{text}\n{html}"

    if URGENCY_WORDS.search(content):
        points += 10; reasons.append("Urgent/pressure wording in body")

    url_regex = re.compile(r"https?://[^\s<>\)\"']+", re.I)
    for m in url_regex.finditer(text or ""):
        links.append(("", m.group(0)))
    for (anchor_text, href) in extract_links_from_html(html or ""):
        if href: links.append((anchor_text or "", href))

    if "<form" in (html or "").lower():
        points += 15; reasons.append("HTML contains a form (possible credential capture)")

    for atext, href in links:
        parsed = urlparse(href)
        host = (parsed.netloc or "").lower()
        reg = extract_registered_domain(host)

        if atext:
            vis_urls = url_regex.findall(atext)
            if vis_urls:
                vis_host = urlparse(vis_urls[0]).netloc.lower()
                vis_reg = extract_registered_domain(vis_host)
                if vis_reg and reg and vis_reg != reg:
                    points += 12; reasons.append(f"Visible link ({vis_reg}) differs from actual link ({reg})")

        if reg in URL_SHORTENERS:
            points += 8; reasons.append(f"URL shortener used: {reg}")
        if is_ip_host(host):
            points += 12; reasons.append(f"URL uses raw IP address: {host}")
        if parsed.port and parsed.port not in (80, 443):
            points += 6; reasons.append(f"URL uses non-standard port: {parsed.port}")
        if looks_punycode(host) or has_non_ascii(host):
            points += 10; reasons.append(f"Suspicious hostname (punycode/non-ASCII): {host}")
        if "@" in parsed.netloc or "@" in parsed.path:
            points += 6; reasons.append(f"'@' present in URL (obfuscation): {href}")

        base_label = reg.split(".")[0] if reg else ""
        for brand, legit in BRAND_DOMAINS.items():
            dist = levenshtein(base_label, brand)
            if 1 <= dist <= 2 and reg not in legit:
                points += 14; reasons.append(f"Potential typosquat: {reg} looks like '{brand}'")

        if reg and reg not in WHITELIST_DOMAINS:
            points += 3; reasons.append(f"External link to non-whitelist domain: {reg}")

    return points, list(dict.fromkeys(reasons)), links

def check_attachments_list(filenames: List[str]) -> Tuple[int, List[str]]:
    points, reasons = 0, []
    for name in filenames:
        low = (name or "").lower()
        for ext in SUSPICIOUS_EXTENSIONS:
            if low.endswith(ext):
                points += 15; reasons.append(f"Suspicious attachment: {name}"); break
    return points, reasons


# ----------------------------
# Scoring + Report
# ----------------------------
def score_to_label(score: int, suspicious_min: int, phish_min: int) -> str:
    if score >= phish_min: return "LIKELY PHISH"
    if score >= suspicious_min: return "SUSPICIOUS"
    return "SAFE"

def analyze_email(msg, suspicious_min: int, phish_min: int) -> Dict:
    subject = safe_decode(msg.get("Subject", ""))
    from_name, from_email = email.utils.parseaddr(msg.get("From", ""))
    text, html = get_body_parts(msg)
    attach = get_attachments(msg)

    score, reasons_total, found_links = 0, [], []

    p, r = check_headers(msg); score += p; reasons_total += r
    p, r, links = check_body(text, html, subject); score += p; reasons_total += r; found_links += links
    p, r = check_attachments_list(attach); score += p; reasons_total += r

    reasons_total = list(dict.fromkeys(reasons_total))  # de-dup, preserve order

    return {
        "subject": subject,
        "from_name": from_name,
        "from_email": from_email,
        "score": score,
        "label": score_to_label(score, suspicious_min, phish_min),
        "reasons": reasons_total,
        "attachments": attach,
        "links": [{"text": t, "href": h} for (t, h) in found_links],
    }

def load_eml_from_bytes(b: bytes):
    return email.message_from_bytes(b)


# ----------------------------
# Streamlit UI
# ----------------------------
st.set_page_config(page_title="Email Phishing Detection Tool", page_icon="🛡️", layout="wide")
st.title("🛡️ Email Phishing Detection Tool")
st.caption("Offline heuristics • Explanations • Links • Attachments")

with st.sidebar:
    st.header("Settings")
    suspicious_min = st.slider("SUSPICIOUS threshold", min_value=10, max_value=60, value=30, step=2)
    phish_min = st.slider("LIKELY PHISH threshold", min_value=40, max_value=100, value=60, step=2)
    st.markdown("---")
    st.markdown("**Tips**")
    st.write("• Upload `.eml` files or paste raw email below.")
    st.write("• Export `.eml` from most mail clients (Gmail/Outlook).")
    st.write("• Adjust thresholds to match your risk tolerance.")

st.subheader("1) Upload .eml file(s)")
files = st.file_uploader("Choose one or more .eml files", type=["eml"], accept_multiple_files=True)

st.subheader("2) Or paste raw email")
raw_text = st.text_area("Paste full raw email (headers + body)", height=180, placeholder="From: ...\nSubject: ...\n...")

results = []
cols = st.columns(1)  # layout spacer

def render_result(idx: int, label_color: str, res: Dict, name: str):
    with st.container(border=True):
        st.markdown(f"**File/Source:** `{name}`")
        st.markdown(f"**Subject:** {res['subject'] or '(none)'}")
        st.markdown(f"**From:** {res['from_name']} <{res['from_email']}>")
        st.markdown(f"**Score:** `{res['score']}`  —  **Label:** <span style='padding:2px 8px;border-radius:8px;background:{label_color};color:white;'>{res['label']}</span>", unsafe_allow_html=True)

        if res.get("attachments"):
            st.markdown("**Attachments:** " + ", ".join(res["attachments"]))
        if res.get("links"):
            st.markdown("**Links found:**")
            st.dataframe([{"anchor_text": x["text"], "href": x["href"]} for x in res["links"]], use_container_width=True)
        st.markdown("**Reasons:**")
        if res["reasons"]:
            for i, r in enumerate(res["reasons"], 1):
                st.write(f"{i:02d}. {r}")
        else:
            st.write("(no flags)")

# Process uploads
if files:
    for f in files:
        try:
            msg = load_eml_from_bytes(f.read())
            res = analyze_email(msg, suspicious_min, phish_min)
            results.append({"source": f.name, **res})
        except Exception as e:
            st.error(f"{f.name}: {e}")

# Process pasted raw email (optional)
if raw_text.strip():
    try:
        msg = email.message_from_string(raw_text)
        res = analyze_email(msg, suspicious_min, phish_min)
        results.append({"source": "pasted_raw_email", **res})
    except Exception as e:
        st.error(f"Raw email parse error: {e}")

# Display results
if results:
    st.subheader("Results")
    label_colors = {"SAFE": "#16a34a", "SUSPICIOUS": "#f59e0b", "LIKELY PHISH": "#dc2626"}
    for i, r in enumerate(results, 1):
        render_result(i, label_colors.get(r["label"], "#334155"), r, r["source"])

    # Download JSON report
    st.markdown("### Export")
    buf = io.BytesIO(json.dumps(results, indent=2, ensure_ascii=False).encode("utf-8"))
    st.download_button("Download JSON report", data=buf, file_name="phish_report.json", mime="application/json")

else:
    st.info("Upload at least one `.eml` or paste a raw email above to analyze.")
