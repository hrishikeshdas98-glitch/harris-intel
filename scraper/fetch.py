#!/usr/bin/env python3
"""
Harris County Motivated Seller Lead Scraper
Scrapes Harris County Clerk portal + HCAD parcel data
"""

import asyncio
import json
import csv
import io
import os
import re
import sys
import time
import zipfile
import logging
import traceback
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional

import requests
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright, TimeoutError as PWTimeout

# ── optional dbfread ──────────────────────────────────────────────────────────
try:
    from dbfread import DBF
    HAS_DBF = True
except ImportError:
    HAS_DBF = False

# ─────────────────────────────────────────────────────────────────────────────
# CONFIG
# ─────────────────────────────────────────────────────────────────────────────
CLERK_URL   = "https://www.cclerk.hctx.net/PublicRecords.aspx"
HCAD_SEARCH = "https://hcad.org/hcad-resources/hcad-appraisal-codes-and-data-download/"
HCAD_BULK   = "https://pdata.hcad.org/download/2024.html"   # fallback index

LOOK_BACK_DAYS = 7
MAX_RETRIES    = 3
RETRY_DELAY    = 3

# Doc-type categories we collect
DOC_TYPES = {
    "LP":      ("Lis Pendens",          "lis_pendens"),
    "NOFC":    ("Notice of Foreclosure","foreclosure"),
    "TAXDEED": ("Tax Deed",             "tax_deed"),
    "JUD":     ("Judgment",             "judgment"),
    "CCJ":     ("Certified Judgment",   "judgment"),
    "DRJUD":   ("Domestic Judgment",    "judgment"),
    "LNCORPTX":("Corp Tax Lien",        "tax_lien"),
    "LNIRS":   ("IRS Lien",             "tax_lien"),
    "LNFED":   ("Federal Lien",         "tax_lien"),
    "LN":      ("Lien",                 "lien"),
    "LNMECH":  ("Mechanic Lien",        "lien"),
    "LNHOA":   ("HOA Lien",             "lien"),
    "MEDLN":   ("Medicaid Lien",        "lien"),
    "PRO":     ("Probate Document",     "probate"),
    "NOC":     ("Notice of Commencement","notice"),
    "RELLP":   ("Release Lis Pendens",  "release"),
}

CAT_LABELS = {
    "lis_pendens": "Lis Pendens",
    "foreclosure": "Pre-Foreclosure",
    "tax_deed":    "Tax Deed",
    "judgment":    "Judgment / Lien",
    "tax_lien":    "Tax Lien",
    "lien":        "Lien",
    "probate":     "Probate / Estate",
    "notice":      "Notice of Commencement",
    "release":     "Release",
}

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)]
)
log = logging.getLogger("scraper")

# ─────────────────────────────────────────────────────────────────────────────
# HELPERS
# ─────────────────────────────────────────────────────────────────────────────
def retry(fn, *args, attempts=MAX_RETRIES, delay=RETRY_DELAY, **kwargs):
    """Call fn(*args, **kwargs) up to `attempts` times, sleeping `delay`s between tries."""
    last_err = None
    for i in range(attempts):
        try:
            return fn(*args, **kwargs)
        except Exception as exc:
            last_err = exc
            log.warning(f"Attempt {i+1}/{attempts} failed: {exc}")
            if i < attempts - 1:
                time.sleep(delay)
    raise last_err


def parse_amount(text: str) -> Optional[float]:
    """Extract dollar amount from a string."""
    if not text:
        return None
    text = re.sub(r"[^\d.]", "", text.replace(",", ""))
    try:
        v = float(text)
        return v if v > 0 else None
    except ValueError:
        return None


def name_variants(name: str) -> list[str]:
    """Return lookup variants: 'FIRST LAST', 'LAST FIRST', 'LAST, FIRST'."""
    name = name.strip().upper()
    variants = {name}
    if "," in name:
        parts = [p.strip() for p in name.split(",", 1)]
        variants.add(f"{parts[1]} {parts[0]}")
        variants.add(f"{parts[0]} {parts[1]}")
    else:
        parts = name.split()
        if len(parts) >= 2:
            variants.add(f"{parts[-1]}, {' '.join(parts[:-1])}")
            variants.add(f"{parts[-1]} {' '.join(parts[:-1])}")
    return list(variants)


def score_record(rec: dict) -> tuple[int, list[str]]:
    """Compute seller score 0-100 and return list of flags."""
    flags  = []
    score  = 30  # base

    cat = rec.get("cat", "")
    doc = rec.get("doc_type", "")

    if cat == "lis_pendens":
        flags.append("Lis pendens")
    if cat == "foreclosure":
        flags.append("Pre-foreclosure")
    if cat in ("judgment", "tax_lien", "lien"):
        flags.append("Judgment lien" if "jud" in doc.lower() else
                     "Tax lien"      if "tax" in doc.lower() or "irs" in doc.lower() or "fed" in doc.lower() else
                     "Mechanic lien" if "mech" in doc.lower() else
                     "Judgment lien")
    if cat == "probate":
        flags.append("Probate / estate")

    owner = rec.get("owner", "")
    if owner and re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST|ASSOC)\b", owner, re.I):
        flags.append("LLC / corp owner")

    # filed date → new this week
    try:
        filed = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d")
        if (datetime.now() - filed).days <= 7:
            flags.append("New this week")
            score += 5
    except Exception:
        pass

    score += 10 * len(flags)

    # LP + FC combo
    all_types = [rec.get("cat", "")]
    if "lis_pendens" in all_types and "foreclosure" in all_types:
        score += 20

    amount = rec.get("amount")
    if amount:
        if amount > 100_000:
            score += 15
        elif amount > 50_000:
            score += 10

    if rec.get("prop_address"):
        score += 5

    return min(score, 100), flags

# ─────────────────────────────────────────────────────────────────────────────
# HCAD PARCEL LOOKUP
# ─────────────────────────────────────────────────────────────────────────────
class ParcelDB:
    """Download and index the HCAD bulk parcel data."""

    def __init__(self):
        self.index: dict[str, dict] = {}   # upper-name → parcel row

    # ── download helpers ──────────────────────────────────────────────────────
    def _find_download_url(self) -> Optional[str]:
        """Scrape HCAD download page to find the current parcel DBF/CSV zip."""
        candidates = [
            HCAD_BULK,
            "https://pdata.hcad.org/download/2025.html",
            "https://hcad.org/hcad-resources/hcad-appraisal-codes-and-data-download/",
        ]
        for url in candidates:
            try:
                r = requests.get(url, timeout=30)
                soup = BeautifulSoup(r.text, "lxml")
                for a in soup.find_all("a", href=True):
                    href = a["href"]
                    lower = href.lower()
                    if ("real_acct" in lower or "building_res" in lower or "parcel" in lower) \
                            and (".zip" in lower or ".dbf" in lower):
                        if href.startswith("http"):
                            return href
                        return f"https://pdata.hcad.org{href}"
            except Exception as exc:
                log.warning(f"HCAD page {url} failed: {exc}")
        return None

    def _download_zip(self, url: str) -> Optional[bytes]:
        log.info(f"Downloading HCAD bulk data from {url}")
        for attempt in range(MAX_RETRIES):
            try:
                r = requests.get(url, timeout=120, stream=True)
                r.raise_for_status()
                return r.content
            except Exception as exc:
                log.warning(f"Download attempt {attempt+1} failed: {exc}")
                time.sleep(RETRY_DELAY)
        return None

    # ── DBF / CSV parsers ─────────────────────────────────────────────────────
    def _load_dbf_bytes(self, data: bytes, filename: str) -> list[dict]:
        if not HAS_DBF:
            log.warning("dbfread not installed; skipping DBF parse")
            return []
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".dbf", delete=False) as f:
            f.write(data)
            tmp = f.name
        try:
            table = DBF(tmp, encoding="latin-1", ignore_missing_memofile=True)
            return [dict(row) for row in table]
        finally:
            os.unlink(tmp)

    def _load_csv_bytes(self, data: bytes) -> list[dict]:
        text = data.decode("latin-1", errors="replace")
        reader = csv.DictReader(io.StringIO(text))
        return [row for row in reader]

    def _row_to_parcel(self, row: dict) -> dict:
        """Normalise column names across DBF variants."""
        def g(*keys):
            for k in keys:
                v = row.get(k) or row.get(k.upper()) or row.get(k.lower())
                if v and str(v).strip():
                    return str(v).strip()
            return ""

        return {
            "owner":      g("OWNER","OWN1","OWNR","OWNER_NAME"),
            "site_addr":  g("SITE_ADDR","SITEADDR","SITE_ADDRESS","STR_ADDR"),
            "site_city":  g("SITE_CITY","SITECITY","CITY"),
            "site_zip":   g("SITE_ZIP","SITEZIP","ZIP"),
            "mail_addr":  g("ADDR_1","MAILADR1","MAIL_ADDR","MAILING_ADDR"),
            "mail_city":  g("CITY","MAILCITY","MAIL_CITY"),
            "mail_state": g("STATE","MAILSTATE","MAIL_STATE"),
            "mail_zip":   g("ZIP","MAILZIP","MAIL_ZIP"),
        }

    # ── public interface ──────────────────────────────────────────────────────
    def load(self):
        url = self._find_download_url()
        if not url:
            log.warning("Could not find HCAD bulk download URL; parcel data unavailable")
            return

        raw = self._download_zip(url)
        if not raw:
            log.warning("Failed to download HCAD data")
            return

        rows: list[dict] = []
        try:
            zf = zipfile.ZipFile(io.BytesIO(raw))
            for name in zf.namelist():
                low = name.lower()
                data = zf.read(name)
                if low.endswith(".dbf"):
                    rows.extend(self._load_dbf_bytes(data, name))
                elif low.endswith(".csv") and ("acct" in low or "parcel" in low):
                    rows.extend(self._load_csv_bytes(data))
        except zipfile.BadZipFile:
            # maybe the download itself is a DBF or CSV
            if url.lower().endswith(".dbf"):
                rows = self._load_dbf_bytes(raw, url)
            else:
                rows = self._load_csv_bytes(raw)

        log.info(f"Loaded {len(rows):,} parcel rows from HCAD")
        for row in rows:
            p = self._row_to_parcel(row)
            owner = p["owner"]
            if owner:
                for v in name_variants(owner):
                    self.index.setdefault(v, p)

    def lookup(self, owner_name: str) -> Optional[dict]:
        for v in name_variants(owner_name):
            if v in self.index:
                return self.index[v]
        return None

# ─────────────────────────────────────────────────────────────────────────────
# CLERK SCRAPER  (Playwright async)
# ─────────────────────────────────────────────────────────────────────────────
class ClerkScraper:
    """
    Scrapes the Harris County Clerk Public Records portal.
    Uses Playwright for JS-heavy pages that rely on __doPostBack.
    """

    def __init__(self, start_date: datetime, end_date: datetime):
        self.start = start_date
        self.end   = end_date
        self.records: list[dict] = []

    async def run(self) -> list[dict]:
        async with async_playwright() as pw:
            browser = await pw.chromium.launch(headless=True, args=["--no-sandbox"])
            ctx = await browser.new_context(
                user_agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
            )
            page = await ctx.new_page()
            page.set_default_timeout(60_000)

            for doc_code in DOC_TYPES:
                try:
                    await self._search_doc_type(page, doc_code)
                except Exception:
                    log.error(f"Error scraping {doc_code}:\n{traceback.format_exc()}")

            await browser.close()
        return self.records

    async def _search_doc_type(self, page, doc_code: str):
        log.info(f"Searching clerk for doc type: {doc_code}")
        label, cat = DOC_TYPES[doc_code]

        for attempt in range(MAX_RETRIES):
            try:
                await page.goto(CLERK_URL, wait_until="domcontentloaded")
                break
            except PWTimeout:
                if attempt == MAX_RETRIES - 1:
                    raise
                await asyncio.sleep(RETRY_DELAY)

        # ── Fill the search form ──────────────────────────────────────────────
        # The portal uses ASP.NET WebForms with __doPostBack.
        # We interact via visible form controls.

        # Try to set doc type dropdown
        try:
            await page.select_option("select[id*='DocType'], select[name*='DocType']", doc_code)
        except Exception:
            # Some portals have a text search instead of dropdown
            try:
                await page.fill("input[id*='DocType'], input[name*='DocType']", doc_code)
            except Exception:
                log.warning(f"Could not set doc type for {doc_code}")

        # Date range
        start_str = self.start.strftime("%m/%d/%Y")
        end_str   = self.end.strftime("%m/%d/%Y")
        try:
            await page.fill("input[id*='StartDate'], input[name*='StartDate'], input[id*='FromDate']", start_str)
            await page.fill("input[id*='EndDate'],   input[name*='EndDate'],   input[id*='ToDate']",   end_str)
        except Exception:
            log.warning("Could not fill date range fields")

        # Submit
        try:
            await page.click("input[type='submit'], button[type='submit']")
            await page.wait_for_load_state("networkidle", timeout=45_000)
        except Exception:
            # Try __doPostBack
            try:
                await page.evaluate("__doPostBack('btnSearch','')")
                await page.wait_for_load_state("networkidle", timeout=45_000)
            except Exception as exc:
                log.warning(f"Submit failed for {doc_code}: {exc}")
                return

        # ── Paginate results ─────────────────────────────────────────────────
        page_num = 1
        while True:
            html = await page.content()
            rows = self._parse_results_html(html, doc_code, cat, label)
            self.records.extend(rows)
            log.info(f"  {doc_code} page {page_num}: {len(rows)} rows (total {len(self.records)})")

            # Next page?
            next_btn = await page.query_selector("a:has-text('Next'), input[value='Next']")
            if not next_btn:
                break
            try:
                await next_btn.click()
                await page.wait_for_load_state("networkidle", timeout=30_000)
                page_num += 1
            except Exception:
                break

    def _parse_results_html(self, html: str, doc_code: str, cat: str, label: str) -> list[dict]:
        soup = BeautifulSoup(html, "lxml")
        rows = []

        # Look for any result table
        tables = soup.find_all("table")
        for tbl in tables:
            headers = [th.get_text(strip=True).lower() for th in tbl.find_all("th")]
            if not any(h in headers for h in ("doc#", "document", "filed", "grantor", "grantee", "type")):
                continue

            for tr in tbl.find_all("tr")[1:]:
                tds = tr.find_all("td")
                if len(tds) < 3:
                    continue
                try:
                    row = self._extract_row(tds, headers, doc_code, cat, label)
                    if row:
                        rows.append(row)
                except Exception:
                    continue
        return rows

    def _extract_row(self, tds, headers: list, doc_code: str, cat: str, label: str) -> Optional[dict]:
        def cell(idx_or_key):
            if isinstance(idx_or_key, int):
                return tds[idx_or_key].get_text(strip=True) if idx_or_key < len(tds) else ""
            for i, h in enumerate(headers):
                if idx_or_key in h and i < len(tds):
                    return tds[i].get_text(strip=True)
            return ""

        # Try to find a link for the document
        link = ""
        for td in tds:
            a = td.find("a", href=True)
            if a:
                href = a["href"]
                if href.startswith("http"):
                    link = href
                else:
                    link = f"https://www.cclerk.hctx.net/{href.lstrip('/')}"
                break

        doc_num  = cell("doc") or cell(0)
        filed    = self._parse_date(cell("filed") or cell("date") or cell(2))
        grantor  = cell("grantor") or cell("owner") or cell(3)
        grantee  = cell("grantee") or cell(4)
        legal    = cell("legal") or cell("description") or cell(5)
        amount   = parse_amount(cell("amount") or cell("consideration") or cell(6))

        if not doc_num:
            return None

        return {
            "doc_num":    doc_num,
            "doc_type":   doc_code,
            "filed":      filed,
            "cat":        cat,
            "cat_label":  CAT_LABELS.get(cat, label),
            "owner":      grantor,
            "grantee":    grantee,
            "amount":     amount,
            "legal":      legal,
            "prop_address": "",
            "prop_city":    "Houston",
            "prop_state":   "TX",
            "prop_zip":     "",
            "mail_address": "",
            "mail_city":    "",
            "mail_state":   "",
            "mail_zip":     "",
            "clerk_url":    link or self._build_clerk_url(doc_num),
            "flags":        [],
            "score":        0,
        }

    def _parse_date(self, text: str) -> str:
        for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y"):
            try:
                return datetime.strptime(text.strip(), fmt).strftime("%Y-%m-%d")
            except Exception:
                continue
        return text.strip()

    def _build_clerk_url(self, doc_num: str) -> str:
        return f"https://www.cclerk.hctx.net/PublicRecords.aspx?DocNum={doc_num}"

# ─────────────────────────────────────────────────────────────────────────────
# STATIC FALLBACK SCRAPER  (requests + BeautifulSoup)
# Used when Playwright session can't authenticate or times out
# ─────────────────────────────────────────────────────────────────────────────
class StaticClerkScraper:
    """
    Falls back to direct HTTP requests. Some clerk portals have a REST/JSON
    endpoint used by their own JS that we can hit directly.
    """

    BASE = "https://www.cclerk.hctx.net"
    SEARCH = "/Applications/WebSearch/PR.aspx"  # common real-property path

    def __init__(self, start: datetime, end: datetime):
        self.start = start
        self.end   = end
        self.session = requests.Session()
        self.session.headers.update({
            "User-Agent": "Mozilla/5.0 (compatible; LeadScraper/1.0)"
        })
        self.records: list[dict] = []

    def run(self) -> list[dict]:
        # Fetch index page to grab ASP.NET viewstate tokens
        try:
            r = retry(self.session.get, self.BASE + self.SEARCH, timeout=30)
            soup = BeautifulSoup(r.text, "lxml")
            viewstate = self._hidden(soup, "__VIEWSTATE")
            event_val  = self._hidden(soup, "__EVENTVALIDATION")
        except Exception as exc:
            log.error(f"StaticClerkScraper init failed: {exc}")
            return []

        for doc_code in DOC_TYPES:
            try:
                recs = self._search(doc_code, viewstate, event_val)
                self.records.extend(recs)
            except Exception:
                log.error(f"StaticClerkScraper {doc_code}:\n{traceback.format_exc()}")

        return self.records

    def _hidden(self, soup, name: str) -> str:
        el = soup.find("input", {"name": name})
        return el["value"] if el else ""

    def _search(self, doc_code: str, viewstate: str, event_val: str) -> list[dict]:
        label, cat = DOC_TYPES[doc_code]
        payload = {
            "__VIEWSTATE":       viewstate,
            "__EVENTVALIDATION": event_val,
            "__EVENTTARGET":     "",
            "__EVENTARGUMENT":   "",
            "DocType":           doc_code,
            "StartDate":         self.start.strftime("%m/%d/%Y"),
            "EndDate":           self.end.strftime("%m/%d/%Y"),
            "btnSearch":         "Search",
        }
        r = retry(self.session.post,
                  self.BASE + self.SEARCH,
                  data=payload, timeout=60)
        soup = BeautifulSoup(r.text, "lxml")
        return self._parse(soup, doc_code, cat, label)

    def _parse(self, soup: BeautifulSoup, doc_code: str, cat: str, label: str) -> list[dict]:
        rows = []
        for tbl in soup.find_all("table"):
            hdrs = [th.get_text(strip=True).lower() for th in tbl.find_all("th")]
            if not hdrs:
                continue
            for tr in tbl.find_all("tr")[1:]:
                tds = tr.find_all("td")
                if len(tds) < 3:
                    continue
                try:
                    doc_num = tds[0].get_text(strip=True)
                    if not doc_num:
                        continue
                    link = ""
                    a = tds[0].find("a", href=True)
                    if a:
                        href = a["href"]
                        link = href if href.startswith("http") else f"{self.BASE}/{href.lstrip('/')}"

                    filed = tds[1].get_text(strip=True) if len(tds) > 1 else ""
                    grantor = tds[2].get_text(strip=True) if len(tds) > 2 else ""
                    grantee = tds[3].get_text(strip=True) if len(tds) > 3 else ""
                    legal   = tds[4].get_text(strip=True) if len(tds) > 4 else ""
                    amount  = parse_amount(tds[5].get_text(strip=True)) if len(tds) > 5 else None

                    rows.append({
                        "doc_num":    doc_num,
                        "doc_type":   doc_code,
                        "filed":      filed,
                        "cat":        cat,
                        "cat_label":  CAT_LABELS.get(cat, label),
                        "owner":      grantor,
                        "grantee":    grantee,
                        "amount":     amount,
                        "legal":      legal,
                        "prop_address": "",
                        "prop_city":    "Houston",
                        "prop_state":   "TX",
                        "prop_zip":     "",
                        "mail_address": "",
                        "mail_city":    "",
                        "mail_state":   "",
                        "mail_zip":     "",
                        "clerk_url":    link or f"{self.BASE}/PublicRecords.aspx?DocNum={doc_num}",
                        "flags":        [],
                        "score":        0,
                    })
                except Exception:
                    continue
        return rows

# ─────────────────────────────────────────────────────────────────────────────
# GHL CSV EXPORT
# ─────────────────────────────────────────────────────────────────────────────
def export_ghl_csv(records: list[dict], path: str):
    columns = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]

    Path(path).parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=columns)
        writer.writeheader()
        for r in records:
            owner = r.get("owner", "")
            parts = owner.replace(",", "").split()
            first = parts[0] if parts else ""
            last  = " ".join(parts[1:]) if len(parts) > 1 else ""

            writer.writerow({
                "First Name":            first,
                "Last Name":             last,
                "Mailing Address":       r.get("mail_address", ""),
                "Mailing City":          r.get("mail_city", ""),
                "Mailing State":         r.get("mail_state", ""),
                "Mailing Zip":           r.get("mail_zip", ""),
                "Property Address":      r.get("prop_address", ""),
                "Property City":         r.get("prop_city", ""),
                "Property State":        r.get("prop_state", ""),
                "Property Zip":          r.get("prop_zip", ""),
                "Lead Type":             r.get("cat_label", ""),
                "Document Type":         r.get("doc_type", ""),
                "Date Filed":            r.get("filed", ""),
                "Document Number":       r.get("doc_num", ""),
                "Amount/Debt Owed":      r.get("amount", ""),
                "Seller Score":          r.get("score", 0),
                "Motivated Seller Flags": " | ".join(r.get("flags", [])),
                "Source":                "Harris County Clerk",
                "Public Records URL":    r.get("clerk_url", ""),
            })

    log.info(f"GHL CSV saved → {path}")

# ─────────────────────────────────────────────────────────────────────────────
# MAIN
# ─────────────────────────────────────────────────────────────────────────────
async def main():
    end_date   = datetime.now()
    start_date = end_date - timedelta(days=LOOK_BACK_DAYS)
    log.info(f"Date range: {start_date.date()} → {end_date.date()}")

    # ── 1. Clerk scrape ───────────────────────────────────────────────────────
    log.info("Starting Playwright clerk scrape…")
    records: list[dict] = []
    try:
        scraper = ClerkScraper(start_date, end_date)
        records = await scraper.run()
        log.info(f"Playwright scrape: {len(records)} records")
    except Exception:
        log.error(f"Playwright failed:\n{traceback.format_exc()}")

    if not records:
        log.info("Trying static HTTP fallback…")
        try:
            static = StaticClerkScraper(start_date, end_date)
            records = static.run()
            log.info(f"Static scrape: {len(records)} records")
        except Exception:
            log.error(f"Static scrape also failed:\n{traceback.format_exc()}")

    # Deduplicate by doc_num
    seen: set[str] = set()
    unique: list[dict] = []
    for r in records:
        key = r.get("doc_num", "")
        if key and key not in seen:
            seen.add(key)
            unique.append(r)
    records = unique
    log.info(f"Unique records after dedup: {len(records)}")

    # ── 2. HCAD parcel lookup ─────────────────────────────────────────────────
    log.info("Loading HCAD parcel data…")
    parcel_db = ParcelDB()
    try:
        parcel_db.load()
    except Exception:
        log.error(f"Parcel load error:\n{traceback.format_exc()}")

    for r in records:
        owner = r.get("owner", "")
        if owner:
            p = parcel_db.lookup(owner)
            if p:
                r["prop_address"] = p.get("site_addr", "")
                r["prop_city"]    = p.get("site_city", "Houston") or "Houston"
                r["prop_state"]   = "TX"
                r["prop_zip"]     = p.get("site_zip", "")
                r["mail_address"] = p.get("mail_addr", "")
                r["mail_city"]    = p.get("mail_city", "")
                r["mail_state"]   = p.get("mail_state", "TX") or "TX"
                r["mail_zip"]     = p.get("mail_zip", "")

    # ── 3. Score & flag ───────────────────────────────────────────────────────
    for r in records:
        score, flags = score_record(r)
        r["score"] = score
        r["flags"] = flags

    records.sort(key=lambda x: x["score"], reverse=True)

    with_address = sum(1 for r in records if r.get("prop_address"))
    log.info(f"Records with address: {with_address}/{len(records)}")

    # ── 4. Build output JSON ──────────────────────────────────────────────────
    output = {
        "fetched_at":  datetime.utcnow().isoformat() + "Z",
        "source":      "Harris County Clerk - cclerk.hctx.net",
        "date_range":  {
            "start": start_date.strftime("%Y-%m-%d"),
            "end":   end_date.strftime("%Y-%m-%d"),
        },
        "total":        len(records),
        "with_address": with_address,
        "records":      records,
    }

    for path in ["dashboard/records.json", "data/records.json"]:
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            json.dump(output, f, indent=2, default=str)
        log.info(f"Saved → {path}")

    # ── 5. GHL CSV ────────────────────────────────────────────────────────────
    today = datetime.now().strftime("%Y%m%d")
    export_ghl_csv(records, f"data/ghl_export_{today}.csv")

    log.info("✅ Scrape complete.")

if __name__ == "__main__":
    asyncio.run(main())
