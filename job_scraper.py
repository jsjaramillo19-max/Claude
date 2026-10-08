#!/usr/bin/env python3
"""
Daily job scraper for part-time bookkeeper / accountant roles.
Targets remote-friendly positions matching a Xero-certified CPA profile
based in the Philippines (NZ/AU cross-border experience).

Usage:
    python3 job_scraper.py              # scrape and open report
    python3 job_scraper.py --no-open    # scrape without opening

Output: job_reports/jobs_YYYY-MM-DD.html  (sorted newest-first)
State:  job_reports/seen_jobs.json        (dedup across runs)
"""

import json, os, re, sys, hashlib, subprocess, warnings, webbrowser, time, random
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from html import escape as html_escape, unescape as html_unescape
from pathlib import Path
from urllib.parse import quote_plus

import requests
from bs4 import BeautifulSoup, XMLParsedAsHTMLWarning
warnings.filterwarnings("ignore", category=XMLParsedAsHTMLWarning)
from dateutil import parser as dateparser

try:
    from jobspy import scrape_jobs as jobspy_scrape
    HAS_JOBSPY = True
except ImportError:
    HAS_JOBSPY = False

# ── Config ──────────────────────────────────────────────────────────────

SEARCH_TERMS = [
    "bookkeeper",
    "bookkeeping",
    "bookkeeper part time",
    "xero bookkeeper",
    "accountant part time",
    "accountant remote",
    "accounts payable",
    "accounts receivable",
    "bank reconciliation",
    "staff accountant remote",
    "accounting clerk",
    "tax preparer",
    "tax preparer remote",
    "tax assistant",
    "tax associate remote",
    "tax preparation philippines",
    "us tax preparer",
    "finance assistant remote",
    "audit associate remote",
]

RELEVANCE_KEYWORDS = {
    # Higher weight = stronger CV match
    # Flexible hours / part-time (TOP PRIORITY — user wants these first)
    "flexible": 10,
    "flexible hours": 10,
    "flex schedule": 10,
    "own hours": 8,
    "set your own hours": 10,
    "work at your own pace": 8,
    "anytime": 6,
    "part-time": 8,
    "part time": 8,
    "20 hours": 6,
    "25 hours": 6,
    "15 hours": 6,
    "10 hours": 6,
    "contract": 3,
    "freelance": 3,
    # Core bookkeeping skills
    "xero": 5,
    "bookkeeper": 4,
    "bookkeeping": 4,
    "reconciliation": 3,
    "bank reconciliation": 4,
    "accounts payable": 3,
    "accounts receivable": 3,
    "ap/ar": 3,
    "invoicing": 3,
    "month-end": 3,
    "journal entries": 3,
    "ledger": 2,
    "catch-up": 3,
    "cleanup": 3,
    "financial statements": 3,
    # Accounting / audit
    "accountant": 3,
    "accounting": 2,
    "staff accountant": 3,
    "cpa": 4,
    "audit": 2,
    "financial reporting": 3,
    "general ledger": 3,
    # Tax / compliance
    "gst": 4,
    "tax return": 3,
    "tax preparation": 3,
    "bas": 3,
    "compliance": 2,
    "us tax": 3,
    "form 1040": 3,
    "tax preparer": 3,
    "tax assistant": 3,
    "tax associate": 3,
    "tax filing": 3,
    "tax season": 2,
    "tax engagement": 2,
    "irs": 2,
    # Geography match
    "new zealand": 4,
    "nz": 3,
    "australia": 3,
    "au": 1,
    "philippines": 2,
    # Tools
    "dext": 3,
    "hubspot": 1,
    "quickbooks": 2,
    "myob": 2,
    "sage": 1,
    # Remote / work arrangement
    "remote": 2,
    "work from home": 2,
    "virtual": 1,
    # Payroll
    "payroll": 2,
}

EXCLUDE_PATTERNS = [
    r"\bvp\b",
    r"\bin-office only\b",
    r"\bon-?site only\b",
    r"\bon-?site\b",
    r"\bprimarily on-?site\b",
    r"\bhybrid.{0,10}on-?site\b",
    r"\bin.office\b",
    r"\bwork from office\b",
    r"\bhybrid\s+(work|set-?up|arrangement|schedule|model|role|position)\b",
    r"\bwork set-?up\s*:?\s*hybrid\b",
    r"\boffice[- ]based\b",
    r"\breport(ing)?\s+to\s+(the|our)\s+office\b",
]

# Boards that only list remote work; every other source must prove the role is remote
REMOTE_ONLY_SOURCES = {
    "RemoteOK", "Remotive", "Himalayas", "WorkingNomads", "WeWorkRemotely",
    "RemoteRocketship", "OnlineJobs.ph", "VirtualStaff.ph", "Hubstaff Talent",
    "Jobicy",
}
REMOTE_LOCATION_MARKERS = ["remote", "anywhere", "worldwide", "work from home", "wfh"]
REMOTE_ROLE_PATTERNS = [
    r"\bfully[- ]remote\b", r"\b100%\s*remote\b", r"\bremote[- ]first\b",
    r"\bremote\s+(position|role|job|work|working|opportunity|set-?up|arrangement|basis|contract|employee|staff|team member)\b",
    r"\bjoin\s+(our|a)\s+(fully\s+)?remote\b",
    r"\bwork(ing)?\s+(from\s+home|remotely)\b", r"\bwork[- ]from[- ]home\b", r"\bwfh\b",
    r"\bhome[- ]?based\b", r"\btelecommut", r"\blocation\s*:?\s*remote\b", r"\(remote\)",
    r"\bremote\s*[-|–,/]\s*(philippines|ph|worldwide|global|anywhere)\b",
    r"\bpermanent(ly)?\s+(wfh|remote)\b",
    r"[-–|(]\s*remote\s*[)|]",
    r"\bwork (set-?up|arrangement)\s*:?\s*(fully |100% |permanent )?(remote|wfh|work from home)",
]


def is_confirmed_remote(job: dict) -> bool:
    loc = (job.get("location") or "").lower()
    if any(k in loc for k in ["hybrid", "on-site", "onsite", "on site"]):
        return False
    source = job.get("source", "")
    if source in REMOTE_ONLY_SOURCES:
        return True
    if any(k in loc for k in REMOTE_LOCATION_MARKERS):
        return True
    if re.search(r"\bremote\b", (job.get("title") or "").lower()):
        return True
    text = f"{job.get('title', '')} {job.get('description', '')}".lower()
    return any(re.search(p, text) for p in REMOTE_ROLE_PATTERNS)

GEO_EXCLUDE = [
    "us only", "u.s. only", "us-only", "united states only",
    "us-based only", "u.s.-based only", "must be located in the us",
    "must reside in the us", "must reside in the u.s",
    "us residents only", "u.s. residents only",
    "usa only", "us citizens only",
    "must be based in the united states",
    "uk only", "united kingdom only", "uk-based only",
    "eu only", "europe only", "eu-based only",
    "canada only", "canadian residents only",
    "must be authorized to work in the u",
    "work authorization required",
    "no visa sponsorship",
    "must be located in the united states",
    "this role is only open to candidates in the us",
    "open to us-based", "open to u.s.-based",
    "based in the us", "based in the u.s",
    "located in the us", "located in the u.s",
    "must be in the us", "must be in the u.s",
    "professional based in the us",
    "latam-based", "latam based", "latam only", "latin america only", "based in latam", "based in latin america",
    "remote (latam)", "remote - latam", "open to latam", "candidates in latam", "emea only", "emea-based",
    "north america only", "americas only", "europe-based only", "must be based in europe", "must be based in canada",
    "right to work in new zealand", "right to work in nz",
    "nz citizen or resident", "nz citizen or permanent resident",
    "new zealand citizen or", "nz residency", "must be based in new zealand",
    "must be based in nz", "must reside in new zealand", "must be located in new zealand",
    "right to work in australia", "australian citizen or permanent resident",
    "must be based in australia", "must reside in australia",
]

# Signals that a "remote" job is actually US-remote (needs US tax residency)
US_EMPLOYMENT_SIGNALS = [
    "401(k)", "401k", "401 k",
    "health insurance", "dental insurance", "vision insurance",
    "medical insurance", "benefits package including medical",
    "paid holidays", "pto policy", "paid time off",
    "w-2", "w2 employee",
    "normal business hours",
    "us business hours",
    "eastern time", "pacific time", "central time",
    "eeo ", "equal opportunity employer",
]
US_EMPLOYMENT_THRESHOLD = 3

GEO_INCLUDE = [
    "worldwide", "global remote", "globally distributed",
    "international candidates", "international applicants",
    "open internationally",
    "philippines", "asia", "apac", "south east asia", "southeast asia",
    "remote - any location", "remote - worldwide",
    "all countries", "any country", "any location",
    "oceania", "asia pacific", "asia-pacific",
    "open to candidates anywhere", "hire anywhere",
    "location: anywhere", "anywhere in the world",
]

TITLE_EXCLUDE = [
    "pharmacist", "nurse", "doctor", "physician", "surgeon", "dentist",
    "therapist", "clinician", "clinical", "medical",
    "developer", "engineer", "designer", "architect",
    "marketing", "sales rep", "sales manager",
    "driver", "mechanic", "technician", "electrician", "plumber",
    "chef", "cook", "bartender", "waiter",
    "teacher", "professor", "instructor",
    "recruiter", "talent acquisition",
    "customer service", "call center",
    "data scientist", "machine learning",
    "product manager", "project manager",
    "hr manager", "human resources",
    "construction", "warehouse",
    "contract administrator", "procurement", "quantity surveyor",
    "finance manager", "regional finance", "finance director",
    "android", "ios ", "frontend", "backend", "fullstack", "full stack",
    "supply chain", "logistics",
    "customer care", "content growth", "test manager",
]

# AI-training / model-evaluation gigs, which the user does not want. A job that merely uses AI tools is fine.
AI_TRAINING_TITLE = re.compile(
    r"\bAI[ -](train\w*|tutor\w*|model\w*|data|evaluat\w*|review\w*|annotat\w*|rater|task)\b|\b(train|training|evaluat\w+) AI\b"
    r"|\(AI training\)|data (annotat|label)\w*|\bLLM\b|model (review|evaluat|quality)\w*|task author|search (engine )?evaluator|maps? evaluator", re.I)

# TITLE_EXCLUDE entries that name a different job (not an industry), so they block even accounting-looking titles
ROLE_EXCLUDE = {
    "developer", "engineer", "designer", "architect", "sales rep", "sales manager", "recruiter", "talent acquisition",
    "customer service", "call center", "customer care", "data scientist", "machine learning", "product manager",
    "project manager", "hr manager", "finance manager", "regional finance", "finance director", "teacher", "professor",
    "instructor", "android", "ios ", "frontend", "backend", "fullstack", "full stack", "test manager", "content growth",
}

REPORT_DIR = Path(__file__).parent / "job_reports"
SEEN_FILE = REPORT_DIR / "seen_jobs.json"
USER_AGENTS = [
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/125.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.5 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:128.0) Gecko/20100101 Firefox/128.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14.5; rv:128.0) Gecko/20100101 Firefox/128.0",
]

def _headers() -> dict:
    return {
        "User-Agent": random.choice(USER_AGENTS),
        "Accept": "text/html,application/xhtml+xml,application/json",
        "Accept-Language": "en-US,en;q=0.9",
    }

HEADERS = _headers()
REQUEST_TIMEOUT = 30


MAX_AGE_DAYS = 7
# Fresh roles only: the user is risk-averse and time-limited, so apply where odds are best (<= 7 days).
# (Was 30 for rare NZ/AU + careers-page roles; raise it back if the list feels too thin.)
NICHE_MAX_AGE_DAYS = 7
NICHE_PATTERN = re.compile(r"new zealand|\bnz\b|australia|\bau/nz\b|\bnz/au\b")


# ── Helpers ─────────────────────────────────────────────────────────────

def job_id(title: str, company: str, url: str) -> str:
    raw = f"{title.lower().strip()}|{company.lower().strip()}|{url.strip()}"
    return hashlib.sha256(raw.encode()).hexdigest()[:16]


def relevance_score(title: str, description: str, location: str = "") -> int:
    text = f"{title} {description} {location}".lower()
    score = 0
    for kw, weight in RELEVANCE_KEYWORDS.items():
        if kw in text:
            score += weight
    if any(g in text for g in ["worldwide", "anywhere", "global", "international", "any location", "all countries"]):
        score += 3
    if "philippines" in text:
        score += 5
    return score


def busyness_rating(title: str, description: str) -> tuple[int, str]:
    """Estimate how busy/demanding a job is (1-5 scale). Returns (score, label)."""
    text = f"{title} {description}".lower()
    score = 3.0
    if any(k in text for k in ["full-time", "full time", "40 hours", "45 hours", "40hrs", "8 hours a day"]):
        score += 1.5
    if any(k in text for k in ["part-time", "part time"]):
        score -= 1.0
    if any(re.search(r"\b" + k + r"\b", text) for k in ["5 hours", "10 hours", "15 hours", "5hrs", "10hrs", "15hrs", "few hours"]):
        score -= 1.5
    if any(re.search(r"\b" + k + r"\b", text) for k in ["20 hours", "25 hours", "20hrs", "25hrs", "half time"]):
        score -= 0.5
    if any(re.search(r"\b" + k + r"\b", text) for k in ["30 hours", "35 hours", "30hrs", "35hrs"]):
        score += 0.5
    if any(k in text for k in ["multiple clients", "multi-client", "several clients", "multiple entities", "multi-entity"]):
        score += 1.0
    # Multiple companies / wearing many hats
    if any(k in text for k in ["two companies", "two growing", "multiple companies", "both companies", "two businesses", "multiple businesses"]):
        score += 1.0
    if any(k in text for k in ["operations", "operations &", "office manager", "executive assistant"]):
        score += 0.5
    if any(k in text for k in ["virtual assistant", "va ", " va,", "admin support", "administrative"]):
        score += 0.3
    title_lower = title.lower()
    hats = sum(1 for k in ["bookkeep", "account", "admin", "operation", "assistant", "payroll", "hr ", "marketing", "customer service", "social media"] if k in title_lower)
    if hats >= 2:
        score += 0.5
    if any(k in text for k in ["high volume", "fast-paced", "fast paced", "high-volume", "demanding", "heavy workload"]):
        score += 1.0
    if any(k in text for k in ["urgent", "asap", "immediately", "tight deadline", "time-sensitive"]):
        score += 0.5
    if any(k in text for k in ["own pace", "at your own pace", "no rush", "relaxed", "low volume"]):
        score -= 1.0
    if any(k in text for k in ["flexible", "flex schedule", "own hours", "set your own hours", "anytime"]):
        score -= 0.5
    if any(k in text for k in ["one-time", "one time", "single project", "small project", "quick project", "simple task"]):
        score -= 1.0
    if any(k in text for k in ["ongoing", "long-term", "long term", "permanent"]):
        score += 0.3
    if any(k in text for k in ["manager", "lead", "supervisor", "team lead", "oversee"]):
        score += 0.5
    if any(k in text for k in ["data entry", "simple bookkeeping", "basic bookkeeping", "basic accounting"]):
        score -= 0.5
    s = max(1, min(5, round(score)))
    labels = {1: "Light", 2: "Easy", 3: "Moderate", 4: "Busy", 5: "Heavy"}
    return s, labels[s]


def acceptance_probability(title: str, description: str, location: str, tags: list[str] = None) -> int:
    """Estimate % chance of getting accepted, accounting for competition."""
    text = f"{title} {description} {location} {' '.join(tags or [])}".lower()
    # Skill match (how well your CV fits the requirements)
    skill = 0
    if any(k in text for k in ["xero", "dext"]):
        skill += 20
    if any(k in text for k in ["bookkeeper", "bookkeeping"]):
        skill += 10
    if any(k in text for k in ["cpa", "certified public accountant"]):
        skill += 8
    if any(k in text for k in ["nz", "new zealand", "australia", "au cross-border", "nz/au", "au/nz"]):
        skill += 15
    if any(k in text for k in ["gst", "bas", "ird", "ato"]):
        skill += 10
    if any(k in text for k in ["audit", "assurance"]):
        skill += 5
    if any(k in text for k in ["reconciliation", "bank reconciliation", "month-end"]):
        skill += 5
    if any(k in text for k in ["quickbooks", "myob", "sage"]):
        skill += 3
    if any(k in text for k in ["financial statements", "financial reporting", "ledger", "general ledger"]):
        skill += 4
    if any(k in text for k in ["tax return", "tax preparation", "tax preparer", "tax accountant", "form 1040", "us tax", "tax compliance"]):
        skill += 8
    # Eligibility boosters
    elig = 0
    if any(k in text for k in ["philippines", "ph-based", "filipino"]):
        elig += 8
    if any(k in text for k in ["worldwide", "anywhere", "global", "any location", "all countries"]):
        elig += 3
    if any(k in text for k in ["flexible", "part-time", "part time", "own hours"]):
        elig += 3
    # Competition penalty (more applicants = harder to land)
    comp = 0
    if any(k in text for k in ["onlinejobs", "philippines"]):
        comp += 15
    if any(k in text for k in ["remote", "work from home", "wfh"]):
        comp += 8
    if any(k in text for k in ["entry level", "junior", "no experience"]):
        comp += 10
    # Barriers
    barrier = 0
    if re.search(r"\b(senior|lead|manager|cfo|controller)\b", text):
        barrier += 5
    if any(k in text for k in ["us only", "must be in us", "us-based only", "us citizen"]):
        barrier += 40
    if any(k in text for k in ["5+ years", "10+ years", "7+ years"]):
        barrier += 3
    if any(k in text for k in ["3+ years"]):
        barrier += 1
    # "Remote" without real international hiring signals = likely US-remote
    us_remote_signals = sum(1 for s in [
        "federal holiday", "company retreat", "annual retreat",
        "401(k)", "401k", "health insurance", "dental insurance", "vision insurance",
        "w-2", "w2", "pto policy", "paid time off",
        "equal opportunity employer", "eeo ",
    ] if s in text)
    ph_friendly_signals = any(k in text for k in [
        "philippines", "filipino", "asia", "apac", "southeast asia",
        "international", "globally", "worldwide team",
        "contractor", "independent contractor", "freelance",
        "any country", "all countries",
    ])
    if us_remote_signals >= 2 and not ph_friendly_signals:
        barrier += 15
    elif us_remote_signals >= 1 and not ph_friendly_signals:
        barrier += 5
    # Required tool mismatch (QBO-only roles when user is Xero-certified)
    qbo_required = any(k in text for k in ["quickbooks online expert", "qbo proadvisor", "qbo certification",
                                            "quickbooks expert", "must have quickbooks", "quickbooks required"])
    has_xero = any(k in text for k in ["xero"])
    if qbo_required and not has_xero:
        barrier += 12
    # Niche bonus (fewer competing applicants for specialized roles)
    niche = 0
    if any(k in text for k in ["servicem8", "dext", "ignition"]):
        niche += 8
    if skill >= 30 and any(k in text for k in ["nz", "new zealand", "au/nz", "nz/au"]):
        niche += 5
    raw = 20 + min(skill, 40) + min(elig, 12) + niche - comp - barrier
    return max(5, min(80, raw))


US_STATE_ABBREVS = {
    "al", "ak", "az", "ar", "ca", "co", "ct", "de", "fl", "ga",
    "hi", "id", "il", "in", "ia", "ks", "ky", "la", "me", "md",
    "ma", "mi", "mn", "ms", "mo", "mt", "ne", "nv", "nh", "nj",
    "nm", "ny", "nc", "nd", "oh", "ok", "or", "pa", "ri", "sc",
    "sd", "tn", "tx", "ut", "vt", "va", "wa", "wv", "wi", "wy", "dc",
}


def _has_us_state_abbrev(location: str) -> bool:
    """Detect US state abbreviations like 'Cabin John, MD' or 'Austin, TX (On-site)'."""
    m = re.search(r",\s*([A-Z]{2})\b", location)
    if m and m.group(1).lower() in US_STATE_ABBREVS:
        return True
    return False


def _count_us_employment_signals(text: str) -> int:
    return sum(1 for s in US_EMPLOYMENT_SIGNALS if s in text)


def is_geo_restricted(title: str, description: str, location: str) -> bool:
    text = f"{title} {description} {location}".lower()
    if any(g in text for g in GEO_EXCLUDE):
        return True
    if any(g in text for g in GEO_INCLUDE):
        return False
    us_signals = _count_us_employment_signals(text)
    has_us_location = _has_us_state_abbrev(location)
    # US state in location + multiple US employment signals = US-remote job
    if has_us_location and us_signals >= 2:
        return True
    # Even without US location, heavy US employment signals = likely US-only
    if us_signals >= US_EMPLOYMENT_THRESHOLD:
        return True
    # Plain US state abbreviation with on-site
    if has_us_location and "on-site" in location.lower():
        return True
    loc = location.lower().strip()
    # "Remote, US" or "Remote, United States" = US-only
    if re.match(r"remote[,\s]+(us|u\.s|united states|usa)\b", loc):
        if not any(g in text for g in GEO_INCLUDE):
            return True
    # US state abbreviation in location (e.g. "Philadelphia, PA") = US-only
    if has_us_location:
        if not any(g in text for g in GEO_INCLUDE):
            return True
    us_only_locations = [
        "united states", "usa",
        "new york", "california", "texas", "florida", "illinois",
        "san francisco", "los angeles", "chicago", "boston", "seattle",
        "denver", "austin", "atlanta", "miami", "portland",
        "washington dc", "d.c.",
        "philadelphia", "dallas", "houston", "phoenix", "minneapolis",
        "indianapolis", "columbus", "charlotte", "san diego",
        "san antonio", "san jose", "jacksonville", "fort worth",
        "nashville", "memphis", "baltimore", "milwaukee",
        "albuquerque", "tucson", "fresno", "sacramento",
        "kansas city", "mesa", "omaha", "raleigh", "colorado springs",
        "long beach", "virginia beach", "oakland", "tampa",
        "tulsa", "arlington", "new orleans", "cleveland", "pittsburgh",
        "st. louis", "st louis", "cincinnati",
    ]
    uk_locations = ["london", "manchester", "birmingham", "united kingdom", "england", "scotland"]
    eu_locations = ["germany", "berlin", "munich", "france", "paris", "amsterdam", "netherlands", "spain", "madrid", "barcelona", "italy"]
    anz_locations = ["new zealand", "auckland", "wellington", "christchurch", "hamilton, waikato",
                     "australia", "sydney", "melbourne", "brisbane", "perth", "adelaide", "canberra"]
    restricted = us_only_locations + uk_locations + eu_locations + anz_locations
    if loc and any(loc == r or loc.startswith(r + ",") or loc.startswith(r + " ") or (", " + r) in loc or r in loc for r in restricted):
        if not any(g in text for g in GEO_INCLUDE):
            return True
    # Vague "Remote" with USD pay and zero PH/international signals = likely US-domestic
    vague_location = loc in ("remote", "remote job", "work from home", "")
    if vague_location:
        ph_friendly = any(k in text for k in [
            "philippines", "filipino", "asia", "apac", "southeast asia",
            "worldwide", "any country",
            "all countries", "offshore", "overseas", "contractor",
            "independent contractor", "freelance",
            "hire anywhere", "anywhere in the world",
            "open internationally", "global remote",
            "international candidates", "international applicants",
        ])
        if not ph_friendly:
            has_usd_pay = bool(re.search(
                r"\$\d[\d,.]*\s*/?\s*"
                r"(hr|hour|an hour|per hour|hourly"
                r"|a week|per week|weekly|/wk|/week"
                r"|a year|per year|yearly|annually|/yr|/year"
                r"|a month|per month|monthly|/mo|/month)",
                text,
            ))
            if has_usd_pay:
                return True
    return False


def is_licensed_legal_role(title: str) -> bool:
    """Attorney/lawyer roles need a bar licence; assistants and paralegals supporting them do not."""
    t = title.lower()
    return bool(re.search(r"\b(attorney|lawyer|counsel|solicitor|barrister)\b", t)) and not re.search(
        r"assistant|paralegal|secretary|support|clerk|\bva\b|virtual|intake|coordinator|to (an? |the )?(attorney|lawyer)", t)


def is_excluded(title: str, description: str, location: str = "") -> bool:
    text = f"{title} {description}".lower()
    title_lower = title.lower()
    if any(re.search(p, text) for p in EXCLUDE_PATTERNS):
        return True
    if AI_TRAINING_TITLE.search(title):
        return True
    blocked = [t for t in TITLE_EXCLUDE if t in title_lower]
    # in an accounting title, an industry word ("Controller, US Construction") describes the employer, not the job
    if blocked and FIRM_FINANCE_TITLE.search(title):
        blocked = [t for t in blocked if t in ROLE_EXCLUDE]
    if blocked:
        return True
    if is_licensed_legal_role(title):
        return True
    if is_geo_restricted(title, description, location):
        return True
    return False


def is_accounting_related(title: str, description: str) -> bool:
    title_lower = title.lower()
    text = f"{title} {description}".lower()
    title_markers = [
        "bookkeep", "accountant", "accounting", "accounts payable",
        "accounts receivable", "xero", "cpa", "auditor", "audit associate",
        "accounting clerk", "finance officer", "finance assistant",
        "financial analyst", "tax accountant", "payroll",
        "controller", "treasurer",
        "tax preparer", "tax assistant", "tax associate",
        "tax analyst", "tax specialist", "tax reviewer",
        "tax manager", "tax senior", "tax staff",
    ]
    if any(m in title_lower for m in title_markers):
        return True
    body_markers = [
        "bookkeep", "reconciliation", "xero", "ledger",
        "ap/ar", "invoicing", "financial statement", "tax return",
        "gst", "journal entr", "quickbooks", "myob", "dext",
        "general ledger", "month-end close", "financial report",
        "tax preparation", "bank rec", "catch-up bookkeep",
        "accounts payable", "accounts receivable",
        "form 1040", "1040", "1120", "1065", "tax filing",
        "tax compliance", "tax workpaper", "tax engagement",
        "tax season", "us tax", "u.s. tax",
    ]
    return any(m in text for m in body_markers)


def extract_pay(text: str) -> str:
    text = text.replace(",", "")
    patterns = [
        r"(?:(?:usd|aud|nzd|cad|gbp)\s?|\b(?:nz|au|a))?\$\s?\d{1,6}(?:\.\d+)?(?:\s?(?:usd|aud|nzd|cad))?(?:\s*[-–]\s*(?:nz|au|a)?\$?\s?\d{1,6}(?:\.\d+)?)?\s*(?:usd|aud|nzd|cad)?\s*(?:per\s+|/\s?|an?\s+)(?:hour|hr|week|month|mo|year|annum|yr)",
        r"\$\s?(\d{2,6})\s*[-–]\s*\$?\s?(\d{2,6})\s*(?:per\s+|/)?(hour|hr|week|month|year|annually|p\.?a\.?|yr)",
        r"\$\s?(\d{2,6})\s*(?:per\s+|/)?(hour|hr|week|month|year|annually|p\.?a\.?|yr)",
        r"(\d{2,3})k\s*[-–]\s*(\d{2,3})k",
        r"USD\s?\$?\s?(\d{2,6})\s*[-–]\s*\$?\s?(\d{2,6})",
        r"(?:(?:aud|nzd|usd|cad|gbp|eur|sgd|php|a\$|nz\$|₱)\s?)?(\d{2,6})\s*[-–]\s*(\d{2,6})\s*(?:per\s+|/)?(hour|hr|week|month|year)",
    ]
    for p in patterns:
        m = re.search(p, text, re.IGNORECASE)
        if m:
            return m.group(0).strip()
    return ""


PHP_RATES = {
    "usd": 56, "aud": 37, "nzd": 34, "gbp": 71, "eur": 62,
    "cad": 41, "sgd": 42, "hkd": 7.2, "php": 1, "₱": 1,
}

def _monthly_php_range(raw_pay: str, hours_per_week: float | None = None) -> tuple[float, float] | None:
    """Monthly PHP (low, high) for a salary string, or None if it has no usable number."""
    if not raw_pay:
        return None
    text = raw_pay.lower().replace(",", "").replace(" ", "")
    # explicit currency codes win over a bare "$", so "NZD $13-$18/hr" is NZD, not USD
    currency_rate = next((rate for cur, rate in PHP_RATES.items() if cur in text), None)
    if currency_rate is None:
        currency_rate = PHP_RATES["nzd"] if "nz$" in text else PHP_RATES["aud"] if re.search(r"(^|[^a-z])(a|au)\$", text) else PHP_RATES["usd"]
    if "php" in text or "₱" in text:
        currency_rate = 1
    nums = re.findall(r"(\d+(?:\.\d+)?)", text)
    if not nums:
        return None
    vals = [float(n) for n in nums[:2]]
    # a bare figure like "50000" with no currency sign (common on OnlineJobs.ph) is pesos per month
    if not re.search(r"\$|usd|aud|nzd|gbp|eur|cad|sgd|hkd|php|₱|k\b", text) and min(vals) >= 10000:
        return min(vals), max(vals)
    if any(k in text for k in ["k/yr", "k/year", "kpa", "k p.a"]):
        vals = [v * 1000 for v in vals]
    avg = sum(vals) / len(vals)
    # text has spaces stripped, so "per month" arrives as "permonth"
    if any(k in text for k in ["/hr", "/hour", "perhour", "anhour", "hourly"]):
        factor = (hours_per_week or 40) * 4
    elif any(k in text for k in ["/wk", "/week", "perweek", "aweek", "weekly"]):
        factor = 4.33
    elif any(k in text for k in ["/mo", "permonth", "amonth", "monthly"]):
        factor = 1
    elif any(k in text for k in ["/yr", "/year", "peryear", "ayear", "yearly", "annually", "p.a", "perannum"]):
        factor = 1 / 12
    elif any(k in text for k in ["k-", "k/"]) and avg > 20:
        factor = 1000 / 12
    elif avg > 5000 and currency_rate != 1:
        factor = 1 / 12
    else:
        factor = 1
    php = sorted(v * factor * currency_rate for v in vals)
    return php[0], php[-1]


def normalize_pay(raw_pay: str) -> str:
    """Convert salary text to monthly PHP estimate for comparison."""
    rng = _monthly_php_range(raw_pay)
    if not rng:
        return raw_pay or ""
    php_monthly = sum(rng) / 2
    if php_monthly >= 1000:
        return f"~₱{php_monthly:,.0f}/mo"
    return raw_pay


HIGH_PAY_MIN_USD = 2000
HIGH_PAY_MAX_USD = 15000


def job_pay_text(j: dict) -> str:
    return (j.get("salary") or extract_pay(f"{j['title']} {j.get('description', '')}")
            or extract_pay((j.get("_full_text") or j.get("full_description") or "")[:6000]))


def monthly_usd_range(j: dict) -> tuple[float, float] | None:
    """Monthly USD (low, high). Hourly rates use the posting's stated weekly hours, else full-time."""
    text = f"{j['title']} {j.get('description', '')} {(j.get('_full_text') or j.get('full_description') or '')[:6000]}"
    m = re.search(r"(\d{1,2})\s*(?:[-–]\s*\d{1,2}\s*)?(?:hours?|hrs?)\s*(?:per|a|/|each)\s*week", text, re.I)
    hours = float(m.group(1)) if m and 1 <= int(m.group(1)) <= 60 else None
    rng = _monthly_php_range(job_pay_text(j), hours)
    if not rng or rng[1] < 500:
        return None
    return rng[0] / PHP_RATES["usd"], rng[1] / PHP_RATES["usd"]


def parse_date_fuzzy(raw: str | None) -> datetime | None:
    if not raw:
        return None
    try:
        return dateparser.parse(raw)
    except (ValueError, OverflowError):
        return None


def freshness_label(dt: datetime | None) -> str:
    if not dt:
        return "Unknown"
    now = datetime.now(timezone.utc)
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    delta = now - dt
    if delta.days == 0:
        hours = delta.seconds // 3600
        if hours == 0:
            return "Just now"
        return f"{hours}h ago"
    if delta.days == 1:
        return "Yesterday"
    if delta.days < 7:
        return f"{delta.days}d ago"
    return f"{delta.days}d ago"


def load_seen() -> dict:
    if SEEN_FILE.exists():
        return json.loads(SEEN_FILE.read_text())
    return {}


def save_seen(seen: dict):
    SEEN_FILE.write_text(json.dumps(seen, indent=2))


# ── Scrapers ────────────────────────────────────────────────────────────

def scrape_remoteok() -> list[dict]:
    """RemoteOK public JSON API."""
    jobs = []
    try:
        resp = requests.get(
            "https://remoteok.com/api",
            headers={**HEADERS, "Accept": "application/json"},
            timeout=REQUEST_TIMEOUT,
        )
        resp.raise_for_status()
        data = resp.json()
        if isinstance(data, list):
            data = data[1:]  # first element is metadata
        for item in data:
            title = item.get("position", "")
            desc = item.get("description", "")
            if not is_accounting_related(title, desc):
                continue
            sal_min = item.get("salary_min", "")
            sal_max = item.get("salary_max", "")
            salary = f"${sal_min}-${sal_max}" if sal_min and sal_max else ""
            jobs.append({
                "title": title,
                "company": item.get("company", ""),
                "url": item.get("url", ""),
                "location": item.get("location", "Remote"),
                "date_raw": item.get("date", ""),
                "date": parse_date_fuzzy(item.get("date")),
                "description": BeautifulSoup(desc, "html.parser").get_text()[:500],
                "tags": item.get("tags", []),
                "salary": salary,
                "source": "RemoteOK",
            })
    except Exception as e:
        print(f"  [RemoteOK] error: {e}")
    return jobs


def scrape_remotive() -> list[dict]:
    """Remotive public API."""
    jobs = []
    categories = ["finance-legal", "all-others", "hr", "customer-support"]
    for cat in categories:
        try:
            resp = requests.get(
                f"https://remotive.com/api/remote-jobs?category={cat}&limit=100",
                headers=HEADERS,
                timeout=REQUEST_TIMEOUT,
            )
            resp.raise_for_status()
            for item in resp.json().get("jobs", []):
                title = item.get("title", "")
                desc = item.get("description", "")
                if not is_accounting_related(title, desc):
                    continue
                required = item.get("candidate_required_location") or ""
                if required and not re.search(r"worldwide|anywhere|global|philippines|asia|apac", required, re.I):
                    continue
                jobs.append({
                    "title": title,
                    "salary": item.get("salary") or "",
                    "company": item.get("company_name", ""),
                    "url": item.get("url", ""),
                    "location": f"{required or 'Worldwide'} (Remote)",
                    "date_raw": item.get("publication_date", ""),
                    "date": parse_date_fuzzy(item.get("publication_date")),
                    "description": BeautifulSoup(desc, "html.parser").get_text()[:500],
                    "tags": [],
                    "source": "Remotive",
                })
        except Exception as e:
            print(f"  [Remotive/{cat}] error: {e}")
    return jobs


def scrape_jobicy() -> list[dict]:
    """Jobicy public API (worldwide remote board). jobGeo names the region a role is open to, so only
    worldwide/anywhere/Philippines/APAC listings are kept; US/UK/EU-locked ones are dropped."""
    jobs, seen = [], set()
    # the accounting-finance industry feed, plus keyword tags for the user's core skills
    searches = [
        {"industry": "accounting-finance"},
        {"tag": "bookkeeper"},
        {"tag": "accountant"},
        {"tag": "xero"},
    ]
    for params in searches:
        try:
            resp = requests.get(
                "https://jobicy.com/api/v2/remote-jobs",
                params={"count": 50, **params},
                headers={**HEADERS, "Accept": "application/json"},
                timeout=REQUEST_TIMEOUT,
            )
            resp.raise_for_status()
            for item in resp.json().get("jobs", []):
                url = item.get("url", "")
                title = item.get("jobTitle", "")
                if not url or url in seen:
                    continue
                desc = item.get("jobDescription", "") or item.get("jobExcerpt", "") or ""
                if not is_accounting_related(title, desc):
                    continue
                geo = str(item.get("jobGeo", "") or "")
                # an empty/"anywhere" geo means worldwide; otherwise the region must include the Philippines/APAC
                if geo and not re.search(r"worldwide|anywhere|global|philippines|asia|apac|oceania", geo, re.I):
                    continue
                seen.add(url)
                job_type = item.get("jobType")
                tags = job_type if isinstance(job_type, list) else ([job_type] if job_type else [])
                jobs.append({
                    "title": title,
                    "company": item.get("companyName", ""),
                    "url": url,
                    "location": f"{geo or 'Worldwide'} (Remote)",
                    "date_raw": item.get("pubDate", ""),
                    "date": parse_date_fuzzy(item.get("pubDate")),
                    "description": BeautifulSoup(desc, "html.parser").get_text()[:500],
                    "tags": tags,
                    "salary": "",
                    "source": "Jobicy",
                })
        except Exception as e:
            print(f"  [Jobicy/{params}] error: {e}")
    return jobs


def scrape_himalayas() -> list[dict]:
    """Himalayas.app public API."""
    jobs = []
    queries = ["bookkeeper", "xero bookkeeper", "accountant part time", "accountant remote", "accounting"]
    for q in queries:
        try:
            resp = requests.get(
                f"https://himalayas.app/jobs/api",
                params={"q": q, "limit": 50},
                headers=HEADERS,
                timeout=REQUEST_TIMEOUT,
            )
            resp.raise_for_status()
            data = resp.json()
            items = data.get("jobs", []) if isinstance(data, dict) else []
            for item in items:
                if not isinstance(item, dict):
                    continue
                title = str(item.get("title", ""))
                desc = str(item.get("description", "") or item.get("excerpt", "") or "")
                if not is_accounting_related(title, desc):
                    continue
                desc_clean = BeautifulSoup(desc, "html.parser").get_text()[:500]
                slug = item.get("companySlug", "")
                title_slug = title.lower().replace(" ", "-")
                fallback_url = f"https://himalayas.app/companies/{slug}/jobs/{title_slug}" if slug else ""
                # an empty restriction list means the role is open worldwide
                restrictions = [str(r) for r in item.get("locationRestrictions") or []]
                if not restrictions:
                    location = "Worldwide (Remote)"
                elif any(re.search(r"philippines|asia|apac|worldwide|anywhere", r, re.I) for r in restrictions):
                    location = "Philippines (Remote)"
                else:
                    continue
                sal_min = item.get("minSalary")
                sal_max = item.get("maxSalary")
                cur = item.get("currency", "USD")
                period = item.get("salaryPeriod", "")
                salary = ""
                if sal_min and sal_max:
                    salary = f"{cur} {sal_min:,}-{sal_max:,}/{period}" if isinstance(sal_min, (int, float)) else f"{cur} {sal_min}-{sal_max}/{period}"
                jobs.append({
                    "title": title,
                    "company": str(item.get("companyName", "")),
                    "url": item.get("applicationUrl") or item.get("url") or fallback_url,
                    "location": location,
                    "date_raw": str(item.get("pubDate", "")),
                    "date": parse_date_fuzzy(str(item.get("pubDate", ""))),
                    "description": desc_clean,
                    "tags": item.get("categories", []) or [],
                    "salary": salary,
                    "source": "Himalayas",
                })
        except Exception as e:
            print(f"  [Himalayas/{q}] error: {e}")
    return jobs


def scrape_arbeitnow() -> list[dict]:
    """Arbeitnow free job board API."""
    jobs = []
    try:
        resp = requests.get(
            "https://www.arbeitnow.com/api/job-board-api",
            headers=HEADERS,
            timeout=REQUEST_TIMEOUT,
        )
        resp.raise_for_status()
        title_markers = [
            "bookkeep", "accountant", "accounting", "accounts payable",
            "accounts receivable", "xero", "cpa", "audit",
            "accounting clerk", "payroll", "tax accountant",
            "controller", "treasurer", "finance officer",
        ]
        for item in resp.json().get("data", []):
            title = item.get("title", "")
            desc = item.get("description", "")
            if not any(m in title.lower() for m in title_markers):
                continue
            jobs.append({
                "title": title,
                "company": item.get("company_name", ""),
                "url": item.get("url", ""),
                "location": item.get("location", "Remote"),
                "date_raw": item.get("created_at", ""),
                "date": parse_date_fuzzy(str(item.get("created_at", ""))),
                "description": BeautifulSoup(desc, "html.parser").get_text()[:500],
                "tags": item.get("tags", []),
                "source": "Arbeitnow",
            })
    except Exception as e:
        print(f"  [Arbeitnow] error: {e}")
    return jobs




def _linkedin_fetch_description(url: str, max_chars: int | None = 800) -> str:
    """Fetch job description from a LinkedIn job detail page."""
    try:
        clean_url = url.split("?")[0]
        resp = requests.get(clean_url, headers=_headers(), timeout=15)
        if resp.status_code != 200:
            return ""
        soup = BeautifulSoup(resp.content, "html.parser")
        desc_el = soup.find("div", class_="show-more-less-html__markup")
        if desc_el:
            return desc_el.get_text("\n", strip=True)[:max_chars]
        for script in soup.find_all("script", type="application/ld+json"):
            try:
                data = json.loads(script.string)
                if isinstance(data, dict) and data.get("description"):
                    return BeautifulSoup(str(data["description"]), "html.parser").get_text("\n", strip=True)[:max_chars]
            except (json.JSONDecodeError, TypeError):
                pass
    except Exception:
        pass
    return ""


def scrape_linkedin_rss() -> list[dict]:
    """LinkedIn job search (public, no auth required) with description fetching."""
    jobs = []
    queries = [
        ("bookkeeper%20remote%20worldwide", ""),
        ("bookkeeper%20remote%20philippines", ""),
        ("xero%20bookkeeper", ""),
        ("bookkeeper%20remote", "&geoId=103121230"),
        ("accountant%20remote", "&geoId=103121230"),
        ("bookkeeper%20part%20time%20remote", ""),
        ("accountant%20part%20time%20remote", ""),
        ("tax%20preparer%20remote%20philippines", ""),
        ("tax%20preparation%20remote", ""),
        ("new%20zealand%20bookkeeper", "&geoId=103121230"),
        ("nz%20accountant", "&geoId=103121230"),
        ("xero%20accountant%20new%20zealand%20remote", ""),
    ]
    raw_jobs = []
    for q, geo in queries:
        try:
            url = (
                f"https://www.linkedin.com/jobs-guest/jobs/api/seeMoreJobPostings/search"
                f"?keywords={q}&f_TPR=r86400&f_WT=2&start=0{geo}"
            )
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            soup = BeautifulSoup(resp.content, "html.parser")
            for card in soup.find_all("li"):
                title_el = card.find("h3", class_="base-search-card__title")
                company_el = card.find("h4", class_="base-search-card__subtitle")
                link_el = card.find("a", class_="base-card__full-link")
                time_el = card.find("time")
                loc_el = card.find("span", class_="job-search-card__location")
                title = title_el.get_text(strip=True) if title_el else ""
                company = company_el.get_text(strip=True) if company_el else ""
                link = link_el["href"] if link_el and link_el.has_attr("href") else ""
                date_str = time_el.get("datetime", "") if time_el else ""
                location = loc_el.get_text(strip=True) if loc_el else "Remote"
                if not title:
                    continue
                if not is_accounting_related(title, ""):
                    continue
                raw_jobs.append({
                    "title": title,
                    "company": company,
                    "url": link,
                    "location": location,
                    "date_raw": date_str,
                    "date": parse_date_fuzzy(date_str),
                    "tags": [],
                    "source": "LinkedIn",
                })
        except Exception as e:
            print(f"  [LinkedIn/{q}] error: {e}")
    # Dedup by URL before fetching descriptions
    seen_urls = set()
    unique = []
    for j in raw_jobs:
        clean = j["url"].split("?")[0]
        if clean not in seen_urls:
            seen_urls.add(clean)
            unique.append(j)
    # Fetch descriptions (limit to 30 to avoid rate limiting)
    # LinkedIn's guest API ignores the remote filter, so remote status must be read from the description
    for j in unique[:100]:
        time.sleep(random.uniform(0.5, 1.5))
        j["description"] = _linkedin_fetch_description(j["url"])
    for j in unique[100:]:
        j["description"] = ""
    jobs = unique
    return jobs


def scrape_jobstreet_ph(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Jobstreet PH JSON search API, restricted to its Remote work arrangement (id 3)."""
    jobs = []
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "tax preparer", "accounts payable", "payroll", "tax assistant", "junior tax"]
    for q in queries:
        try:
            url = (
                "https://ph.jobstreet.com/api/jobsearch/v5/search"
                f"?siteKey=PH-Main&keywords={requests.utils.quote(q)}"
                "&workarrangement=3&sortmode=ListedDate&page=1&pageSize=30"
            )
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            for item in resp.json().get("data", []):
                arrangements = (item.get("workArrangements") or {}).get("data") or []
                if not any((a.get("label") or {}).get("text") == "Remote" for a in arrangements):
                    continue
                title = item.get("title", "")
                desc = " ".join([item.get("teaser", "")] + list(item.get("bulletPoints") or []))
                if not accept(title, desc):
                    continue
                loc_label = (item.get("locations") or [{}])[0].get("label", "")
                work_types = item.get("workTypes") or []
                if any("part" in w.lower() for w in work_types):
                    desc = f"Part-time. {desc}"
                jobs.append({
                    "title": title,
                    "company": item.get("companyName") or (item.get("advertiser") or {}).get("description", ""),
                    "url": f"https://ph.jobstreet.com/job/{item.get('id')}",
                    "location": (f"{loc_label}, Philippines (Remote)" if loc_label and "philippines" not in loc_label.lower()
                                 else f"{loc_label or 'Philippines'} (Remote)"),
                    "date_raw": item.get("listingDate", ""),
                    "date": parse_date_fuzzy(item.get("listingDate", "")),
                    "description": desc[:800],
                    "salary": item.get("salaryLabel", ""),
                    "tags": work_types,
                    "source": "Jobstreet PH",
                })
        except Exception as e:
            print(f"  [Jobstreet/{q}] error: {e}")
    return jobs


def scrape_onlinejobs_ph(queries: list[str] | None = None, accept=None) -> list[dict]:
    """OnlineJobs.ph - #1 site for PH remote workers."""
    jobs = []
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "accounting", "reconciliation", "tax preparer", "tax preparation", "tax assistant", "junior tax", "hawaii",
               "nz bookkeeper", "nz accountant", "new zealand bookkeeper", "new zealand accountant",
               "au nz accountant", "myob"]
    seen = set()
    # read the first few result pages per keyword, not just page 0, so live roles don't drop between runs
    for q in queries:
        for page in range(3):
            try:
                url = f"https://www.onlinejobs.ph/jobseekers/jobsearch/{page}?jobkeyword={q}&jobcategory=&salary_from=&salary_to="
                resp = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT)
                if resp.status_code != 200:
                    break
                boxes = BeautifulSoup(resp.content, "html.parser").find_all("div", class_="jobpost-cat-box")
                if not boxes:
                    break
                for box in boxes:
                    title_el = box.find("h4")
                    if not title_el:
                        continue
                    badge = title_el.find("span", class_="badge")
                    job_type = badge.get_text(strip=True) if badge else ""
                    if badge:
                        badge.decompose()
                    title = title_el.get_text(strip=True)
                    link_el = box.find("a", href=re.compile(r"/jobseekers/job/"))
                    link = ""
                    if link_el:
                        href = link_el["href"]
                        link = href if href.startswith("http") else f"https://www.onlinejobs.ph{href}"
                    if link and link in seen:
                        continue
                    salary_el = box.find("dd")
                    salary = salary_el.get_text(strip=True) if salary_el else ""
                    desc_el = box.find("div", class_="desc")
                    desc = desc_el.get_text(strip=True)[:500] if desc_el else ""
                    date_el = box.find("p", attrs={"data-temp": True})
                    date_str = date_el.get("data-temp", "") if date_el else ""
                    tag_els = box.find_all("a", class_="badge")
                    tags = [t.get_text(strip=True) for t in tag_els]
                    if not accept(title, desc):
                        continue
                    if link:
                        seen.add(link)
                    jobs.append({
                        "title": f"{title} ({job_type})" if job_type else title,
                        "company": "",
                        "url": link,
                        "location": "Philippines (Remote)",
                        "date_raw": date_str,
                        "date": parse_date_fuzzy(date_str) if date_str else None,
                        "description": desc,
                        "salary": salary,
                        "tags": tags,
                        "source": "OnlineJobs.ph",
                    })
                time.sleep(random.uniform(0.3, 0.7))
            except Exception as e:
                print(f"  [OnlineJobs.ph/{q} p{page}] error: {e}")
                break
    return jobs


def scrape_kalibrr() -> list[dict]:
    """Kalibrr.com - major PH job board."""
    jobs = []
    queries = ["bookkeeper", "accountant", "xero", "accounting clerk", "tax preparer", "tax preparation", "tax assistant"]
    for q in queries:
        try:
            url = f"https://www.kalibrr.com/home/te/{q}/co/Philippines"
            resp = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            soup = BeautifulSoup(resp.content, "html.parser")
            for h2 in soup.find_all("h2", class_="css-1gzvnis"):
                link_el = h2.find("a")
                if not link_el:
                    continue
                title = link_el.get_text(strip=True)
                href = link_el.get("href", "")
                link = href if href.startswith("http") else f"https://www.kalibrr.com{href}"
                card = h2
                for _ in range(5):
                    if card.parent:
                        card = card.parent
                    if card.get("class") and any("rounded" in c for c in card.get("class", [])):
                        break
                company = ""
                company_links = card.find_all("a", class_="k-text-subdued")
                if company_links:
                    company = company_links[0].get_text(strip=True)
                loc_el = card.find("span", class_="k-text-gray-500") or card.find(string=re.compile(r"(Metro Manila|Cebu|Davao|Philippines|Remote|Makati|BGC|Quezon|Pasig|Taguig|Mandaluyong)"))
                location = "Philippines"
                if loc_el:
                    location = loc_el.get_text(strip=True) if hasattr(loc_el, "get_text") else str(loc_el).strip()
                card_tokens = {t.strip().lower() for t in card.get_text("|", strip=True).split("|")}
                if "remote" in card_tokens:
                    location = f"{location} (Remote)"
                elif "hybrid" in card_tokens:
                    location = f"{location} (Hybrid)"
                if not is_accounting_related(title, ""):
                    continue
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": link,
                    "location": location,
                    "date_raw": "",
                    "date": None,
                    "description": "",
                    "tags": [],
                    "source": "Kalibrr",
                })
        except Exception as e:
            print(f"  [Kalibrr/{q}] error: {e}")
    return jobs


def scrape_working_nomads() -> list[dict]:
    """Working Nomads free JSON API."""
    jobs = []
    try:
        resp = requests.get(
            "https://www.workingnomads.com/api/exposed_jobs/?category=finance",
            headers=HEADERS,
            timeout=REQUEST_TIMEOUT,
        )
        resp.raise_for_status()
        data = resp.json()
        if not isinstance(data, list):
            data = data.get("jobs", []) if isinstance(data, dict) else []
        for item in data:
            title = item.get("title", "")
            desc = item.get("description", "")
            if not is_accounting_related(title, desc):
                continue
            jobs.append({
                "title": title,
                "company": item.get("company_name", ""),
                "url": item.get("url", ""),
                "location": item.get("location", "Remote"),
                "date_raw": item.get("pub_date", ""),
                "date": parse_date_fuzzy(item.get("pub_date")),
                "description": BeautifulSoup(str(desc), "html.parser").get_text()[:500],
                "tags": item.get("tags", []) if isinstance(item.get("tags"), list) else [],
                "source": "WorkingNomads",
            })
    except Exception as e:
        print(f"  [WorkingNomads] error: {e}")
    return jobs


def scrape_weworkremotely() -> list[dict]:
    """We Work Remotely RSS feed."""
    jobs = []
    feeds = [
        "https://weworkremotely.com/categories/remote-finance-and-legal-jobs.rss",
        "https://weworkremotely.com/remote-jobs.rss",
    ]
    for feed_url in feeds:
        try:
            resp = requests.get(feed_url, headers=HEADERS, timeout=REQUEST_TIMEOUT, allow_redirects=True)
            if resp.status_code != 200:
                continue
            soup = BeautifulSoup(resp.content, "html.parser")
            for item in soup.find_all("item"):
                title_el = item.find("title")
                title = title_el.get_text() if title_el else ""
                link_el = item.find("link")
                link = link_el.get_text() if link_el else ""
                desc_el = item.find("description")
                desc = desc_el.get_text() if desc_el else ""
                pub_el = item.find("pubdate")
                pub = pub_el.get_text() if pub_el else ""
                region_el = item.find("region")
                region = region_el.get_text() if region_el else "Remote"
                if not is_accounting_related(title, desc):
                    continue
                jobs.append({
                    "title": title,
                    "company": "",
                    "url": link,
                    "location": region,
                    "date_raw": pub,
                    "date": parse_date_fuzzy(pub),
                    "description": BeautifulSoup(desc, "html.parser").get_text()[:500],
                    "tags": [],
                    "source": "WeWorkRemotely",
                })
        except Exception as e:
            print(f"  [WWR] error: {e}")
    return jobs








def scrape_accountingfly() -> list[dict]:
    """Accountingfly - niche accounting job board."""
    jobs = []
    try:
        url = "https://www.accountingfly.com/jobs/?_job_categories=accounting-bookkeeping"
        resp = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT)
        if resp.status_code != 200:
            return jobs
        soup = BeautifulSoup(resp.content, "html.parser")
        for card in soup.find_all("article") or soup.find_all("div", class_="job-listing"):
            title_el = card.find("h2") or card.find("h3") or card.find("a")
            if not title_el:
                continue
            title = title_el.get_text(strip=True)
            link_el = title_el.find("a") if title_el.name != "a" else title_el
            link = ""
            if link_el and link_el.has_attr("href"):
                href = link_el["href"]
                link = href if href.startswith("http") else f"https://www.accountingfly.com{href}"
            company_el = card.find(class_="company") or card.find("span", class_="employer")
            company = company_el.get_text(strip=True) if company_el else ""
            loc_el = card.find(class_="location")
            location = loc_el.get_text(strip=True) if loc_el else "Remote"
            salary_el = card.find(class_="salary")
            salary = salary_el.get_text(strip=True) if salary_el else ""
            if not is_accounting_related(title, ""):
                continue
            jobs.append({
                "title": title,
                "company": company,
                "url": link,
                "location": location,
                "date_raw": "",
                "date": None,
                "description": "",
                "salary": salary,
                "tags": [],
                "source": "Accountingfly",
            })
    except Exception as e:
        print(f"  [Accountingfly] error: {e}")
    return jobs


def scrape_jobspy(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Indeed Philippines via JobSpy. Indeed's own remote flag is unreliable, so remote status is read from the text."""
    if not HAS_JOBSPY:
        return []
    jobs = []
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "tax preparer", "accounts payable", "tax assistant"]
    for q in queries:
        try:
            df = jobspy_scrape(
                site_name=["indeed"],
                search_term=q,
                location="Philippines",
                country_indeed="Philippines",
                results_wanted=30,
                hours_old=168,
                is_remote=True,
            )
            for _, row in df.iterrows():
                title = str(row.get("title", ""))
                company = str(row.get("company", "") or row.get("company_name", "") or "")
                if company == "nan":
                    company = ""
                url = str(row.get("job_url", ""))
                loc = str(row.get("location", "") or "Philippines")
                loc = re.sub(r"\bP\d{2}\b,?\s*", "", loc)
                loc = re.sub(r",?\s*\bPH$", "", loc).strip(", ")
                loc = f"{loc}, Philippines" if loc and "philippines" not in loc.lower() else (loc or "Philippines")
                full_desc = str(row.get("description", "") or "")
                desc = full_desc[:800]
                if is_confirmed_remote({"title": title, "description": full_desc, "location": loc, "source": ""}):
                    loc = f"{loc} (Remote)"
                date_raw = str(row.get("date_posted", "") or "")
                salary_min = row.get("min_amount")
                salary_max = row.get("max_amount")
                interval = str(row.get("interval", "") or "")
                currency = str(row.get("currency", "") or "").upper()
                sym = {"PHP": "₱", "USD": "$", "AUD": "AUD ", "NZD": "NZD "}.get(currency, "₱")
                salary = ""
                try:
                    import math
                    if salary_min and not math.isnan(float(salary_min)) and salary_max and not math.isnan(float(salary_max)):
                        salary = f"{sym}{int(salary_min):,}-{sym}{int(salary_max):,}/{interval}" if interval else f"{sym}{int(salary_min):,}-{sym}{int(salary_max):,}"
                    elif salary_min and not math.isnan(float(salary_min)):
                        salary = f"{sym}{int(salary_min):,}/{interval}" if interval else f"{sym}{int(salary_min):,}"
                except (ValueError, TypeError):
                    salary = ""
                if not title or not url or "login" in url:
                    continue
                if not accept(title, desc):
                    continue
                if is_excluded(title, full_desc, loc):
                    continue
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": url,
                    "location": loc,
                    "date_raw": date_raw,
                    "date": parse_date_fuzzy(date_raw),
                    "description": desc,
                    "full_description": full_desc,
                    "salary": salary,
                    "tags": [],
                    "source": "Indeed PH",
                })
        except Exception as e:
            print(f"  [JobSpy/{q}] error: {e}")
    return jobs


def scrape_remoterocketship() -> list[dict]:
    """RemoteRocketship - PH-filtered remote jobs via __NEXT_DATA__ JSON."""
    jobs = []
    categories = ["bookkeeping", "accounting", "tax-preparation"]
    for cat in categories:
        try:
            url = f"https://www.remoterocketship.com/country/philippines/jobs/{cat}/"
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            m = re.search(r'<script id="__NEXT_DATA__" type="application/json">(.*?)</script>', resp.text)
            if not m:
                continue
            data = json.loads(m.group(1))
            openings = data.get("props", {}).get("pageProps", {}).get("initialJobOpenings", [])
            for item in openings:
                if not isinstance(item, dict):
                    continue
                title = item.get("roleTitle", "")
                company = item.get("company", {}).get("name", "") if isinstance(item.get("company"), dict) else ""
                job_url = item.get("url", "")
                loc = item.get("location", "Remote")
                loc_type = item.get("locationType", "")
                if loc_type:
                    loc = f"{loc} ({loc_type})"
                sal_range = item.get("salaryRange") or {}
                salary = sal_range.get("salaryHumanReadableText", "")
                desc = item.get("twoLineJobDescriptionSummary", "")
                date_raw = item.get("created_at", "")
                emp_type = item.get("employmentType", "")
                if not title or not job_url:
                    continue
                if not is_accounting_related(title, desc):
                    continue
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": job_url,
                    "location": loc,
                    "date_raw": date_raw,
                    "date": parse_date_fuzzy(date_raw),
                    "description": desc[:500],
                    "salary": salary,
                    "tags": [emp_type] if emp_type else [],
                    "source": "RemoteRocketship",
                })
        except Exception as e:
            print(f"  [RemoteRocketship/{cat}] error: {e}")
    return jobs


def scrape_hubstaff_talent() -> list[dict]:
    """Hubstaff Talent - AJAX endpoint with XHR header."""
    jobs = []
    queries = ["bookkeeper", "accountant", "xero", "tax preparer"]
    for q in queries:
        try:
            url = f"https://hubstafftalent.net/search/jobs?search[keywords]={q}&search[countries][]=PH&page=1"
            headers = {
                **_headers(),
                "X-Requested-With": "XMLHttpRequest",
                "Accept": "text/javascript",
            }
            resp = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            js_text = resp.text
            html_match = re.search(r"\$\('#results'\)\.html\(\"(.*)\"\);", js_text, re.DOTALL)
            if not html_match:
                continue
            html_str = html_match.group(1).replace(r"\/", "/").replace(r'\"', '"').replace(r"\n", "\n").replace(r"\t", "\t")
            soup = BeautifulSoup(html_str, "html.parser")
            for card in soup.find_all("div", class_="search-result"):
                title_el = card.find("a", class_="name")
                if not title_el:
                    continue
                title = title_el.get_text(strip=True)
                href = title_el.get("href", "")
                link = f"https://hubstafftalent.net{href}" if href.startswith("/") else href
                company_el = card.find("a", class_="job-agency")
                company = company_el.get_text(strip=True) if company_el else ""
                pay_el = card.find("div", class_="pay-rate")
                pay = pay_el.get_text(strip=True) if pay_el else ""
                loc_el = card.find("span", class_="location")
                loc = loc_el.get_text(strip=True) if loc_el else "Remote"
                desc_el = card.find("div", class_="profil-bio")
                desc = desc_el.get_text(strip=True)[:500] if desc_el else ""
                date_el = card.find("span", class_="a-tooltip")
                date_raw = date_el.get("data-original-title", "") if date_el else ""
                tag_els = card.find_all("a", class_="tag")
                tags = [t.get_text(strip=True) for t in tag_els[:5]]
                if not title or not link:
                    continue
                if not is_accounting_related(title, desc + " " + " ".join(tags)):
                    continue
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": link,
                    "location": loc,
                    "date_raw": date_raw,
                    "date": parse_date_fuzzy(date_raw),
                    "description": desc,
                    "salary": pay,
                    "tags": tags,
                    "source": "Hubstaff Talent",
                })
        except Exception as e:
            print(f"  [Hubstaff/{q}] error: {e}")
    return jobs


def scrape_virtualstaff_ph() -> list[dict]:
    """VirtualStaff.ph - JSON API for PH remote jobs."""
    jobs = []
    queries = ["bookkeeper", "accountant", "xero", "accounting", "tax preparer", "tax preparation", "new zealand", "nz accountant", "tax assistant"]
    for q in queries:
        try:
            api_url = "https://www.virtualstaff.ph/api/external/job-list"
            payload = {
                "limit": 30,
                "skip": 0,
                "query": {"search_text": q},
            }
            resp = requests.post(api_url, json=payload, headers={**_headers(), "Content-Type": "application/json"}, timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            data = resp.json()
            items = data.get("result", {}).get("data", [])
            for item in items:
                if not isinstance(item, dict):
                    continue
                title = item.get("job_title", "") or item.get("job_name", "")
                employer = item.get("created_by", "")
                job_id = item.get("_id", "")
                link = f"https://www.virtualstaff.ph/jobs-in-philippines/{job_id}" if job_id else ""
                salary_usd = item.get("monthly_salary_usd")
                salary_php = item.get("monthly_salary_php")
                salary_hr = item.get("salary_amount")
                salary = ""
                if salary_php:
                    salary = f"₱{int(salary_php):,}/mo"
                elif salary_usd:
                    salary = f"${salary_usd}/mo"
                elif salary_hr:
                    salary = f"${salary_hr}/hr"
                job_type = item.get("job_type", "")
                schedule = item.get("schedule_type", "")
                desc = item.get("job_desc", "") or item.get("job_desc_short", "") or ""
                desc = BeautifulSoup(str(desc), "html.parser").get_text()[:500]
                date_raw = item.get("created_time", "")
                skills = item.get("skills", []) or []
                if not title or not link:
                    continue
                if not is_accounting_related(title, desc + " " + " ".join(skills)):
                    continue
                tags = skills[:5]
                if schedule:
                    tags.insert(0, schedule)
                if job_type:
                    tags.insert(0, job_type.replace("_", " "))
                jobs.append({
                    "title": title,
                    "company": employer,
                    "url": link,
                    "location": "Philippines (Remote)",
                    "date_raw": date_raw,
                    "date": parse_date_fuzzy(date_raw),
                    "description": desc,
                    "salary": salary,
                    "tags": tags,
                    "source": "VirtualStaff.ph",
                })
        except Exception as e:
            print(f"  [VirtualStaff/{q}] error: {e}")
    return jobs


# Companies/recruiters known to post PH-eligible bookkeeping/accounting/tax jobs
LINKEDIN_HIRING_PAGES = [
    "cloud-accountant-staffing",
    "remoteva",
    "bookkeepers-without-borders",
    "theremotegroup",
    "davao-accountants",
    "staff-outsource-solutions",
    "virtuestaff",
    "yempo-solutions",
    "remote-staff",
    "outsourced-ph",
]


def scrape_linkedin_posts() -> list[dict]:
    """Scrape hiring posts from LinkedIn company/recruiter pages (public, no auth)."""
    jobs = []
    seen_urls = set()
    for company in LINKEDIN_HIRING_PAGES:
        try:
            page_url = f"https://www.linkedin.com/company/{company}"
            resp = requests.get(page_url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            post_paths = re.findall(
                r"/posts/(" + re.escape(company) + r"_[a-zA-Z0-9_-]+-activity-\d+-[a-zA-Z0-9_-]+)",
                resp.text,
            )
            unique_paths = list(dict.fromkeys(post_paths))[:5]
            for path in unique_paths:
                post_url = f"https://www.linkedin.com/posts/{path}"
                if post_url in seen_urls:
                    continue
                seen_urls.add(post_url)
                time.sleep(random.uniform(0.5, 1.5))
                try:
                    post_resp = requests.get(post_url, headers=_headers(), timeout=REQUEST_TIMEOUT)
                    if post_resp.status_code != 200:
                        continue
                    post_soup = BeautifulSoup(post_resp.content, "html.parser")
                    post_div = post_soup.find("div", class_="attributed-text-segment-list__container")
                    post_text = post_div.get_text(strip=True)[:800] if post_div else ""
                    og_desc = post_soup.find("meta", {"property": "og:description"})
                    og_text = og_desc.get("content", "") if og_desc else ""
                    desc = post_text or og_text
                    if not desc:
                        continue
                    desc_lower = desc.lower()
                    is_hiring = any(k in desc_lower for k in [
                        "hiring", "looking for", "we need", "open role",
                        "join our team", "apply", "send your cv", "send cv",
                        "job opening", "vacancy", "we're seeking",
                    ])
                    if not is_hiring:
                        continue
                    if not is_accounting_related("", desc):
                        continue
                    title_match = re.search(
                        r"(?:hiring[:\s!]*|looking for[:\s]*|open role[:\s]*)([^\n.!]{5,80})",
                        desc, re.IGNORECASE,
                    )
                    title = title_match.group(1).strip() if title_match else desc[:80]
                    title = re.sub(r"\s+", " ", title)
                    company_name = company.replace("-", " ").title()
                    og_title = post_soup.find("meta", {"property": "og:title"})
                    if og_title:
                        poster = og_title.get("content", "").split(" on LinkedIn")[0].strip()
                        if poster:
                            company_name = poster
                    jobs.append({
                        "title": title[:120],
                        "company": company_name,
                        "url": post_url,
                        "location": "",
                        "date_raw": "",
                        "date": None,
                        "description": desc[:500],
                        "salary": "",
                        "tags": ["linkedin-post"],
                        "source": "LinkedIn Posts",
                    })
                except Exception:
                    continue
        except Exception as e:
            print(f"  [LinkedIn Posts/{company}] error: {e}")
    return jobs


def scrape_workable(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Workable's cross-company job search API, filtered to remote roles in the Philippines."""
    jobs = []
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "tax", "accounts payable"]
    for q in queries:
        try:
            url = (
                "https://jobs.workable.com/api/v1/jobs"
                f"?query={requests.utils.quote(q)}&location=Philippines&workplace=remote"
            )
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            for item in resp.json().get("jobs", []):
                if (item.get("workplace") or "").lower() != "remote":
                    continue
                title = item.get("title", "")
                full_desc = BeautifulSoup(item.get("description") or "", "html.parser").get_text("\n", strip=True)
                desc = full_desc.replace("\n", " ")
                if not accept(title, desc):
                    continue
                loc = item.get("location") or {}
                place = ", ".join(p for p in [loc.get("city"), loc.get("countryName")] if p) or "Philippines"
                emp = item.get("employmentType") or ""
                jobs.append({
                    "title": title,
                    "company": (item.get("company") or {}).get("title", ""),
                    "url": item.get("url", ""),
                    "location": f"{place} (Remote)",
                    "date_raw": item.get("created", ""),
                    "date": parse_date_fuzzy(item.get("created", "")),
                    "description": (f"{emp}. " if emp else "") + desc[:800],
                    "full_description": full_desc,
                    "tags": [emp] if emp else [],
                    "source": "Workable",
                })
        except Exception as e:
            print(f"  [Workable/{q}] error: {e}")
    return jobs


def _relative_age_to_date(text: str) -> datetime | None:
    m = re.search(r"(\d+|an?)\+?\s*(hour|day|week|month)s?\s+ago", text or "", re.I)
    if not m:
        return datetime.now(timezone.utc) if re.search(r"today|just now|hours? ago", text or "", re.I) else None
    n = 1 if m.group(1).lower() in ("a", "an") else int(m.group(1))
    unit = m.group(2).lower()
    days = {"hour": n / 24, "day": n, "week": n * 7, "month": n * 30}[unit]
    return datetime.now(timezone.utc) - timedelta(days=days)


def _jobposting_from_page(url: str) -> dict:
    """Read the schema.org JobPosting embedded in a job page (title, full text, date, eligible countries)."""
    resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
    soup = BeautifulSoup(resp.text, "html.parser")
    for script in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(script.string or "")
        except (json.JSONDecodeError, TypeError):
            continue
        nodes = data.get("@graph", [data]) if isinstance(data, dict) else data
        for node in nodes if isinstance(nodes, list) else []:
            if isinstance(node, dict) and node.get("@type") == "JobPosting":
                reqs = node.get("applicantLocationRequirements") or []
                reqs = reqs if isinstance(reqs, list) else [reqs]
                return {
                    "title": node.get("title", ""),
                    "text": BeautifulSoup(node.get("description") or "", "html.parser").get_text("\n", strip=True),
                    "date": node.get("datePosted", ""),
                    "countries": [str((r or {}).get("name", "")).upper() for r in reqs if isinstance(r, dict)],
                    "remote": node.get("jobLocationType") == "TELECOMMUTE",
                    "company": (node.get("hiringOrganization") or {}).get("name", "") if isinstance(node.get("hiringOrganization"), dict) else "",
                    "employment": node.get("employmentType", ""),
                    "salary": _jsonld_salary(node.get("baseSalary")),
                }
    return {}


def _jsonld_salary(base) -> str:
    """Turn a schema.org baseSalary into text like "USD 600-800 per month"."""
    if not isinstance(base, dict):
        return ""
    value = base.get("value") if isinstance(base.get("value"), dict) else {}
    lo, hi = value.get("minValue") or value.get("value"), value.get("maxValue")
    if not lo:
        return ""
    unit = {"HOUR": "hour", "WEEK": "week", "MONTH": "month", "YEAR": "year"}.get(str(value.get("unitText", "")).upper(), "")
    amount = f"{lo}-{hi}" if hi and hi != lo else f"{lo}"
    return f"{base.get('currency', 'USD')} {amount}" + (f" per {unit}" if unit else "")


INTERNATIONAL_HIRING = re.compile(
    r"philippines|filipino|southeast asia|\bapac\b|\basia\b|offshore|overseas|worldwide|anywhere in the world|work from anywhere"
    r"|globally distributed|distributed (team|company)|any country|all countries|international (team|candidates|applicants|contractors?)"
    r"|independent contractor|contractor (role|position|agreement|basis)", re.I)


def _anywhere_but_us_domestic(countries: list[str], text: str) -> bool:
    """A listing open to "anywhere" (a near-complete country list) is only trusted if the posting itself shows
    international hiring and carries no US employment benefits (401(k), health insurance, W-2, ...)."""
    if len(countries) < 30:
        return False
    return _count_us_employment_signals(text.lower()) >= 1 or not INTERNATIONAL_HIRING.search(text)


def _too_old_to_fetch(title: str, listed: datetime | None) -> bool:
    """Skip opening job pages that filter_jobs would discard anyway (NZ/AU titles get the longer window)."""
    if not listed:
        return False
    days = NICHE_MAX_AGE_DAYS if NICHE_PATTERN.search(title.lower()) else MAX_AGE_DAYS
    return listed < datetime.now(timezone.utc) - timedelta(days=days + 1)


def _fetch_posted_date(url: str) -> datetime | None:
    """Recover a posting date from a job page when the source feed omitted it.

    Prefers the schema.org JobPosting datePosted; falls back to a visible
    "Posted/Updated N days ago" on the page. Returns a tz-aware datetime or None.
    """
    try:
        resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
    except Exception:
        return None
    soup = BeautifulSoup(resp.text, "html.parser")
    # 1) schema.org JobPosting datePosted — the reliable path
    for script in soup.find_all("script", type="application/ld+json"):
        try:
            data = json.loads(script.string or "")
        except (json.JSONDecodeError, TypeError):
            continue
        nodes = data.get("@graph", [data]) if isinstance(data, dict) else data
        for node in nodes if isinstance(nodes, list) else []:
            if isinstance(node, dict) and node.get("@type") == "JobPosting" and node.get("datePosted"):
                try:
                    dt = dateparser.parse(str(node["datePosted"]))
                except (ValueError, OverflowError, TypeError):
                    dt = None
                if dt:
                    return dt if dt.tzinfo else dt.replace(tzinfo=timezone.utc)
    # 2) visible relative age. Prefer one anchored to posted/updated wording; otherwise take the
    #    first hour/day/week/month "ago" on the page (years are excluded, so testimonials won't match).
    text = soup.get_text(" ", strip=True)
    age_token = r"(?:\d+|an?)\+?\s*(?:hour|day|week|month)s?\s+ago"
    anchored = re.search(r"(?:posted|updated|listed|published)\b[^.|\n]{0,40}?" + age_token, text, re.I)
    if anchored:
        return _relative_age_to_date(anchored.group(0))
    m = re.search(age_token, text, re.I)
    return _relative_age_to_date(m.group(0)) if m else None


def backfill_dates(jobs: list[dict]) -> None:
    """Fetch posting dates for keeper jobs whose source feed omitted them.

    Without a date, filter_jobs can't apply the freshness cutoff and the post bypasses
    it entirely (e.g. an 11-day-old listing surviving the 7-day window). We only fetch
    for jobs that already pass the cheap exclude/remote checks, grouped per host so one
    site isn't hammered.
    """
    missing = [j for j in jobs
               if not j.get("date") and j.get("url")
               and not is_excluded(j["title"], j.get("description", ""), j.get("location", ""))
               and is_confirmed_remote(j)]
    if not missing:
        return
    from urllib.parse import urlsplit
    lanes: dict[str, list[dict]] = {}
    for j in missing:
        lanes.setdefault(urlsplit(j["url"]).netloc, []).append(j)

    def run_lane(group: list[dict]) -> None:
        for j in group:
            dt = _fetch_posted_date(j["url"])
            if dt:
                j["date"] = dt
                j["date_raw"] = j.get("date_raw") or "backfilled"
            time.sleep(random.uniform(0.3, 0.7))

    with ThreadPoolExecutor(max_workers=min(10, len(lanes))) as pool:
        list(pool.map(run_lane, lanes.values()))
    got = sum(1 for j in missing if j.get("date"))
    print(f"Backfilled dates: {got}/{len(missing)} undated jobs")


def _ph_eligible(countries: list[str], strict: bool = False) -> bool:
    """strict: the Philippines must be listed explicitly (used for searches not already filtered to the Philippines)."""
    listed = any(c in ("PH", "PHL", "PHILIPPINES") for c in countries)
    return listed or (not countries and not strict)


def scrape_jobgether(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Jobgether's Philippines pages: every offer states which countries may apply (schema.org JobPosting)."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "accounting", "tax-accountant", "payroll"]
    jobs, seen = [], set()
    # the all-regions page adds worldwide roles; offers are kept only if the Philippines is an eligible country
    for q, region in [(q, r) for q in queries for r in ("philippines/", "")]:
        try:
            resp = requests.get(f"https://jobgether.com/remote-jobs/{region}{q}", headers=_headers(), timeout=REQUEST_TIMEOUT)
            soup = BeautifulSoup(resp.text, "html.parser")
            for a in soup.find_all("a", href=re.compile(r"^/offer/[\w-]+$")):
                title = a.get_text(" ", strip=True)
                url = f"https://jobgether.com{a['href']}"
                if not title or title.lower() == "apply" or url in seen or not accept(title, ""):
                    continue
                seen.add(url)
                card = a
                while card.parent is not None and len(str(card.parent)) < 6000:
                    card = card.parent
                age = next((s.get_text(strip=True) for s in card.find_all("span") if "ago" in s.get_text()), "")
                listed = _relative_age_to_date(age)
                if _too_old_to_fetch(title, listed):
                    continue
                time.sleep(random.uniform(0.4, 0.9))
                post = _jobposting_from_page(url)
                if not post or not _ph_eligible(post["countries"], strict=not region):
                    continue
                text = post["text"]
                if _anywhere_but_us_domestic(post["countries"], text):
                    continue
                jobs.append({
                    "title": title,
                    "company": post["company"],
                    "url": url,
                    "location": "Philippines (Remote)" if post["remote"] else "Philippines",
                    "date_raw": post["date"] or age,
                    "date": parse_date_fuzzy(re.sub(r"\s*GMT.*$", "", post["date"])) if post["date"] else listed,
                    "description": (f"{post['employment']}. " if post["employment"] else "") + text.replace("\n", " ")[:800],
                    "full_description": text,
                    "salary": post.get("salary", ""),
                    "tags": [],
                    "source": "Jobgether",
                })
        except Exception as e:
            print(f"  [Jobgether/{q}] error: {e}")
    return jobs


def scrape_builtin(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Built In remote jobs filtered to the Philippines; cards show seniority, pages carry eligible countries."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "xero", "accounting", "tax accountant", "payroll"]
    jobs, seen = [], set()
    for q in queries:
        try:
            url = f"https://builtin.com/jobs/remote?search={requests.utils.quote(q)}&country=PHL"
            soup = BeautifulSoup(requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
            for card in soup.select('[data-id="job-card"]'):
                link = card.select_one('a[data-id="job-card-title"]')
                if not link:
                    continue
                title = link.get_text(" ", strip=True)
                job_url = f"https://builtin.com{link['href']}" if link["href"].startswith("/") else link["href"]
                if job_url in seen or not accept(title, ""):
                    continue
                seen.add(job_url)
                level = next((s.get_text(strip=True) for s in card.select("span.font-barlow")
                              if re.search(r"entry|junior|mid|senior|expert", s.get_text(), re.I)), "")
                age = next((s.get_text(strip=True) for s in card.find_all("span") if re.search(r"\bago\b", s.get_text(), re.I)), "")
                if _too_old_to_fetch(title, _relative_age_to_date(age)):
                    continue
                time.sleep(random.uniform(0.4, 0.9))
                post = _jobposting_from_page(job_url)
                if not post or not _ph_eligible(post["countries"]):
                    continue
                text = post["text"]
                jobs.append({
                    "title": title,
                    "company": post["company"],
                    "url": job_url,
                    "location": "Philippines (Remote)" if post["remote"] else "Philippines",
                    "date_raw": post["date"],
                    "date": parse_date_fuzzy(post["date"]),
                    "description": (f"{level} level. " if level else "") + text.replace("\n", " ")[:800],
                    "full_description": text,
                    "tags": [level] if level else [],
                    "source": "Built In",
                })
        except Exception as e:
            print(f"  [Built In/{q}] error: {e}")
    return jobs


def scrape_toa_global() -> list[dict]:
    """TOA Global (AU/NZ accounting offshoring) job feed; region says whether the clients are ANZ or North American."""
    jobs = []
    try:
        headers = {**_headers(), "Accept": "application/json", "Referer": "https://careers.toaglobal.com/",
                   "Origin": "https://careers.toaglobal.com"}
        resp = requests.post("https://job-board.toaglobal.com/api/getAllJobPost", headers=headers, timeout=REQUEST_TIMEOUT)
        for item in resp.json().get("data", []):
            text = item.get("description") or item.get("crimson_jobsummary") or ""
            arrangement = re.search(r"Work Arrangement:\s*([^\n]+)", text)
            remote = (item.get("location") or "").lower() == "remote" or bool(
                arrangement and re.search(r"remote|wfh|work from home", arrangement.group(1), re.I))
            if not remote:
                continue
            title = item.get("toa_jobcodename") or item.get("crimson_jobtitle") or ""
            if not is_accounting_related(title, text):
                continue
            region = {"ANZ": "ANZ clients", "NA": "US clients"}.get(item.get("mercury_region") or "", "")
            jobs.append({
                "title": f"{title}, {region}" if region else title,
                "company": "TOA Global",
                "url": f"https://careers.toaglobal.com/job_view?vacancyId={item.get('crimson_vacancyid')}",
                "location": "Philippines (Remote)",
                "date_raw": item.get("createdon", ""),
                "date": parse_date_fuzzy(item.get("createdon", "")),
                "description": text.replace("\n", " ")[:800],
                "full_description": text,
                "tags": [t for t in [region, item.get("mercury_category") or ""] if t],
                "source": "TOA Global",
                "careers_page": True,
            })
    except Exception as e:
        print(f"  [TOA Global] error: {e}")
    return jobs


def scrape_4dayweek(queries: list[str] | None = None, accept=None) -> list[dict]:
    """4dayweek.io public job API (a general remote board despite the name), filtered to remote roles in the Philippines."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "accounting", "xero", "payroll"]
    jobs, seen = [], set()
    for q in queries:
        try:
            url = (f"https://4dayweek.io/api/v2/jobs?q={requests.utils.quote(q)}"
                   "&country=Philippines&work_arrangement=remote&limit=100")
            for item in requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT).json().get("data", []):
                title = item.get("title", "")
                # the API's search is fuzzy, so the title has to qualify on its own
                if item.get("url") in seen or not accept(title, ""):
                    continue
                seen.add(item.get("url"))
                text = _html_text(item.get("description"))
                hours = item.get("hours_per_week_max") or item.get("hours_per_week_min")
                schedule = "Part-time" if item.get("schedule_type") == "part_time" else ""
                lead = ". ".join(t for t in [schedule, f"{hours} hours per week" if hours else ""] if t)
                jobs.append({
                    "title": title,
                    "company": (item.get("company") or {}).get("name", "") if isinstance(item.get("company"), dict) else "",
                    "url": item.get("url", ""),
                    "location": "Philippines (Remote)",
                    "date_raw": item.get("posted_at", ""),
                    "date": parse_date_fuzzy(item.get("posted_at", "")),
                    "description": (f"{lead}. " if lead else "") + text.replace("\n", " ")[:800],
                    "full_description": text,
                    "tags": [schedule] if schedule else [],
                    "source": "4 Day Week",
                })
            time.sleep(1.2)
        except Exception as e:
            print(f"  [4 Day Week/{q}] error: {e}")
    return jobs


def scrape_remote_com(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Remote.com job board filtered to the Philippines; job pages state which countries may apply."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "accounting", "xero"]
    jobs, seen = [], set()
    # the unfiltered search adds "Remote Anywhere" roles; each job page says which countries may apply
    for q, country in [(q, c) for q in queries for c in ("&country=PHL", "")]:
        try:
            page = requests.get(f"https://remote.com/jobs/all?query={requests.utils.quote(q)}{country}",
                                headers=_headers(), timeout=REQUEST_TIMEOUT)
            soup = BeautifulSoup(page.text, "html.parser")
            for a in soup.find_all("a", href=re.compile(r"^/jobs/[\w-]+/[\w-]+-j\w+")):
                job_url = f"https://remote.com{a['href']}"
                if job_url in seen:
                    continue
                seen.add(job_url)
                time.sleep(random.uniform(0.4, 0.9))
                post = _jobposting_from_page(job_url)
                if not post or not accept(post["title"], "") or not _ph_eligible(post["countries"], strict=not country):
                    continue
                text = post["text"]
                if _anywhere_but_us_domestic(post["countries"], text):
                    continue
                jobs.append({
                    "title": post["title"],
                    "company": post["company"],
                    "url": job_url,
                    "location": "Philippines (Remote)" if post["remote"] else "Philippines",
                    "date_raw": post["date"],
                    "date": parse_date_fuzzy(post["date"]) if post["date"] else None,
                    "description": text.replace("\n", " ")[:800],
                    "full_description": text,
                    "salary": post.get("salary", ""),
                    "tags": [],
                    "source": "Remote.com",
                })
        except Exception as e:
            print(f"  [Remote.com/{q}] error: {e}")
    return jobs


def scrape_remotefirstjobs(queries: list[str] | None = None, accept=None) -> list[dict]:
    """RemoteFirstJobs aggregates remote roles from company career pages; each job page names the eligible country."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper philippines", "accountant philippines", "accounting philippines", "xero philippines"]
    jobs, seen = [], set()
    for q in queries:
        try:
            page = requests.get(f"https://remotefirstjobs.com/jobs?q={requests.utils.quote(q)}", headers=_headers(), timeout=REQUEST_TIMEOUT)
            soup = BeautifulSoup(page.text, "html.parser")
            for a in soup.find_all("a", href=re.compile(r"/companies/[\w-]+/jobs/[\w-]+")):
                job_url = a["href"] if a["href"].startswith("http") else f"https://remotefirstjobs.com{a['href']}"
                if job_url in seen:
                    continue
                seen.add(job_url)
                time.sleep(random.uniform(0.4, 0.9))
                post = _jobposting_from_page(job_url)
                if not post or not accept(post["title"], "") or not _ph_eligible(post["countries"], strict=True):
                    continue
                text = post["text"]
                jobs.append({
                    "title": post["title"],
                    "company": post["company"],
                    "url": job_url,
                    "location": "Philippines (Remote)" if post["remote"] else "Philippines",
                    "date_raw": post["date"],
                    "date": parse_date_fuzzy(post["date"]) if post["date"] else None,
                    "description": text.replace("\n", " ")[:800],
                    "full_description": text,
                    "salary": post.get("salary", ""),
                    "tags": [],
                    "source": "RemoteFirstJobs",
                })
        except Exception as e:
            print(f"  [RemoteFirstJobs/{q}] error: {e}")
    return jobs


def scrape_bruntwork(queries: list[str] | None = None, accept=None) -> list[dict]:
    """BruntWork careers (remote roles, many for Australian clients). The accounting category is taken whole;
    passing queries=["all"] with an accept filter scans every category by title instead."""
    base = "https://www.bruntworkcareers.co"
    listing = f"{base}/search" if queries else f"{base}/search?category=Accounting%20and%20Finance"
    accept = accept or (lambda title, desc: True)
    jobs = []
    try:
        soup = BeautifulSoup(requests.get(listing, headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
        for a in soup.select('a[href^="/jobs/"]'):
            parts = [p.strip() for p in a.get_text("|", strip=True).split("|") if p.strip()]
            title, job_type = (parts[0] if parts else ""), (parts[1] if len(parts) > 1 else "")
            if not title or not accept(title, ""):
                continue
            time.sleep(random.uniform(0.2, 0.5))
            page = BeautifulSoup(requests.get(base + a["href"], headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
            for tag in page(["script", "style", "nav", "header", "footer"]):
                tag.decompose()
            text = page.get_text("\n", strip=True)
            start = text.find("Role Name")
            text = text[start if start >= 0 else 0:].split("BruntWork will never ask")[0]
            published = re.search(r"Published on\s*\n\s*([A-Za-z]{3} \d{1,2} \d{4})", text)
            jobs.append({
                "title": title,
                "company": "BruntWork",
                "url": base + a["href"],
                "location": "Philippines (Remote)",
                "date_raw": published.group(1) if published else "",
                "date": parse_date_fuzzy(published.group(1)) if published else None,
                "description": (f"{job_type}. " if job_type else "") + text.replace("\n", " ")[:800],
                "full_description": f"{job_type}\n{text}",
                "tags": [job_type] if job_type else [],
                "source": "BruntWork",
                "careers_page": True,
            })
    except Exception as e:
        print(f"  [BruntWork] error: {e}")
    return jobs


def scrape_somewhere(queries: list[str] | None = None, accept=None) -> list[dict]:
    """Somewhere (formerly Support Shepherd) via its RecruitCRM job feed. Postings also target LATAM and South
    Africa, so only those located in the Philippines (or remote and naming the Philippines) are kept."""
    accept = accept or is_accounting_related
    queries = queries or ["bookkeeper", "accountant", "accounting", "accounts"]
    api = "https://albatross.recruitcrm.io/v1/external-pages/jobs-by-account/get?account=somewhere&batch=true"
    headers = {**_headers(), "Origin": "https://recruitcrm.io", "Referer": "https://recruitcrm.io/jobs/somewhere",
               "Content-Type": "application/json"}
    jobs, seen = [], set()
    for q in queries:
        try:
            for offset in (0, 50, 100):
                body = {"limit": 50, "offset": offset, "search_data": q, "onlyJobs": True}
                items = (requests.post(api, headers=headers, json=body, timeout=REQUEST_TIMEOUT).json().get("data") or {}).get("jobs") or []
                for item in items:
                    slug, title = str(item.get("slug", "")), item.get("name", "")
                    # "SU - ..." postings are standing talent pools, not open roles
                    if slug in seen or not title or title.startswith("SU -") or not accept(title, ""):
                        continue
                    seen.add(slug)
                    text = _html_text(item.get("jdtext"))
                    city = item.get("city") or ""
                    in_ph = re.search(r"philippines|manila|cebu|davao|\bPH\b", city, re.I)
                    if not in_ph and not (re.search(r"remote|anywhere|global", city, re.I) and re.search(r"philippines|filipino", text, re.I)):
                        continue
                    posted = datetime.fromtimestamp(int(slug[:13]) / 1000, timezone.utc) if slug[:13].isdigit() else None
                    jobs.append({
                        "title": title,
                        "company": "Somewhere",
                        "url": f"https://recruitcrm.io/apply/{slug}",
                        "location": "Philippines (Remote)" if str(item.get("remote")) == "1" else f"{city}, Philippines",
                        "date_raw": posted.isoformat() if posted else "",
                        "date": posted,
                        "description": text.replace("\n", " ")[:800],
                        "full_description": text,
                        "tags": [],
                        "source": "Somewhere",
                        "careers_page": True,
                    })
                if len(items) < 50:
                    break
                time.sleep(0.5)
        except Exception as e:
            print(f"  [Somewhere/{q}] error: {e}")
    return jobs


def scrape_jobdataapi() -> list[dict]:
    """jobdataapi.com indexes postings straight from company hiring systems. Without a key only the first page
    of each search is available, and its remote flag is loose, so remote status is re-checked from the text."""
    jobs, seen = [], set()
    for q in ["bookkeeper", "accountant", "xero", "accounts payable"]:
        try:
            url = f"https://jobdataapi.com/api/jobs/?title={requests.utils.quote(q)}&has_remote=true&country_code=PH"
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code == 429:
                print("  [jobdataapi] hourly limit for keyless requests reached; skipped this run")
                break
            if resp.status_code != 200:
                continue
            for x in resp.json().get("results", []):
                url, title = x.get("application_url") or "", x.get("title") or ""
                if not url or url in seen or not is_accounting_related(title, ""):
                    continue
                seen.add(url)
                text = _html_text(x.get("description"))
                loc = x.get("location") or "Philippines"
                if "philippines" not in loc.lower():
                    loc = f"{loc}, Philippines"
                if is_confirmed_remote({"title": title, "description": text, "location": loc, "source": ""}):
                    loc = f"{loc} (Remote)" if "remote" not in loc.lower() else loc
                company = x.get("company")
                lo, hi, cur = x.get("salary_min"), x.get("salary_max"), x.get("salary_currency") or ""
                jobs.append({
                    "title": title,
                    "company": company.get("name", "") if isinstance(company, dict) else str(company or ""),
                    "url": url,
                    "location": loc,
                    "date_raw": x.get("published") or "",
                    "date": parse_date_fuzzy(x.get("published")) if x.get("published") else None,
                    "description": text.replace("\n", " ")[:800],
                    "full_description": text,
                    "salary": f"{cur} {lo}-{hi}".strip() if lo and hi else "",
                    "tags": [],
                    "source": "jobdataapi",
                })
            time.sleep(2)
        except Exception as e:
            print(f"  [jobdataapi/{q}] error: {e}")
    return jobs


def scrape_jobsora() -> list[dict]:
    """Jobsora PH aggregates small-agency postings (many AU/Xero). Cards carry a Remote/Hybrid tag and a snippet."""
    jobs, seen = [], set()
    for q in ["remote bookkeeper xero", "remote bookkeeper", "remote accountant australia", "remote bookkeeper new zealand"]:
        try:
            page = requests.get(f"https://ph.jobsora.com/jobs?query={requests.utils.quote(q)}", headers=_headers(), timeout=REQUEST_TIMEOUT)
            for card in BeautifulSoup(page.text, "html.parser").find_all("article"):
                link = card.find("a", href=re.compile(r"/job-\d+"))
                parts = [p.strip() for p in card.get_text("|", strip=True).split("|") if p.strip()]
                if not link or not parts:
                    continue
                tag = parts[0] if parts[0] in ("Remote", "Hybrid", "On-site", "Onsite") else ""
                parts = parts[1:] if tag else parts
                title = parts[0]
                job_url = link["href"].split("?")[0]
                if job_url in seen or not is_accounting_related(title, "") or tag in ("Hybrid", "On-site", "Onsite"):
                    continue
                seen.add(job_url)
                company = parts[1] if len(parts) > 1 else ""
                city = parts[2] if len(parts) > 2 else "Philippines"
                snippet = parts[3] if len(parts) > 3 else ""
                age = next((p for p in parts if re.search(r"\bago\b|today|yesterday", p, re.I)), "")
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": job_url,
                    "location": f"{city}, Philippines (Remote)" if tag == "Remote" else f"{city}, Philippines",
                    "date_raw": age,
                    "date": _relative_age_to_date(age),
                    "description": snippet[:800],
                    "tags": [],
                    "source": "Jobsora PH",
                })
        except Exception as e:
            print(f"  [Jobsora/{q}] error: {e}")
    return jobs


def scrape_caribbeanjobs() -> list[dict]:
    """CaribbeanJobs.com: almost all roles are on-site for local residents, so only accounting titles that say
    remote/work from home are kept, and not when the posting limits applicants to locals or work-permit holders."""
    jobs, seen = [], set()
    for q in ["accountant", "bookkeeper", "accounts", "finance"]:
        try:
            url = f"https://www.caribbeanjobs.com/ShowResults.aspx?Keywords={q}&SortBy=MostRecent&PerPage=100"
            soup = BeautifulSoup(requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
            for a in soup.find_all("a", href=re.compile(r"-Job-\d+\.aspx", re.I)):
                title = a.get_text(" ", strip=True)
                job_url = a["href"] if a["href"].startswith("http") else f"https://www.caribbeanjobs.com{a['href']}"
                if job_url in seen or not FIRM_FINANCE_TITLE.search(title) \
                        or not re.search(r"\bremote\b|work from home|\bwfh\b", title, re.I):
                    continue
                seen.add(job_url)
                page = BeautifulSoup(requests.get(job_url, headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
                for tag in page(["script", "style", "nav", "header", "footer"]):
                    tag.decompose()
                text = page.get_text("\n", strip=True)
                start = text.rfind(title)
                text = text[start if start >= 0 else 0:][:8000]
                if "job is expired" in page.get_text(" ").lower() or re.search(
                        r"caricom|nationals? only|citizens? only|belongers?|locals? only|must (be|hold)[^.]{0,30}(resident|work permit)", text, re.I):
                    continue
                annual = re.search(r"Annual Salary:\s*([A-Z]{0,3}\$?\s?[\d,]+(?:\.\d+)?)", text)
                updated = re.search(r"Updated\s+(\d{2})/(\d{2})/(\d{4})", text)
                jobs.append({
                    "title": title,
                    "company": "",
                    "url": job_url,
                    "location": "Caribbean employer (Remote)",
                    "date_raw": updated.group(0) if updated else "",
                    "date": datetime(int(updated.group(3)), int(updated.group(2)), int(updated.group(1)), tzinfo=timezone.utc) if updated else None,
                    "description": text.replace("\n", " ")[:800],
                    "full_description": text,
                    "salary": f"{annual.group(1)} per year" if annual else "",
                    "tags": [],
                    "source": "CaribbeanJobs",
                })
        except Exception as e:
            print(f"  [CaribbeanJobs/{q}] error: {e}")
    return jobs


# AU/NZ offshore staffing firms that recruit Filipino accountants and publish machine-readable careers feeds.
# Pear Tree, The Back Room and VentureX are the few that post NZ-client roles.
OFFSHORE_FIRM_FEEDS = [
    ("workable", "d2b-1", "Pear Tree"),
    ("workable", "hunt-st", "Hunt St"),
    ("workable", "twoconnect-careers", "Twoconnect"),
    ("teamtailor", "https://careers.backroomop.com/jobs.json", "The Back Room Offshoring"),
    ("teamtailor", "https://careers.hammerjack.com.au/jobs.json", "Hammerjack"),
    ("zoho", "https://accessoffshoring.zohorecruit.com.au", "Access Offshoring"),
    ("zoho", "https://careers.remoteworkmate.com", "Remote Workmate"),
    ("awsm", "https://www.traoffshoring.com.au", "TRA Offshoring"),
    ("venturex", "https://venturex.co.nz", "VentureX"),
    ("connectos", "https://connectos.co/careers/", "ConnectOS"),
    ("workable", "manilarecruitment", "Manila Recruitment"),
    ("workable", "careers-at-sleek", "Sleek"),
    ("workable", "teamified", "Teamified"),
    ("teamtailor", "https://recruitgo.teamtailor.com/jobs.json", "RecruitGo"),
    ("teamtailor", "https://careers.visory.com.au/jobs.json", "Visory"),
    ("zoho", "https://boomering.zohorecruit.com", "Boomering"),
    ("zoho", "https://scale-x.zohorecruit.com", "Scale-X"),
    ("lever", "outsourcedstaff", "Outsourced"),
    ("lever", "getwingapp", "Wing Assistant"),
    ("lever", "levelup", "LevelUp"),
    ("workable", "hireframe", "Hireframe"),
    ("workable", "mod-careers", "MyOutDesk"),
    ("breezy", "sourcefit", "Sourcefit"),
    ("bamboohr", "connectcpa", "ConnectCPA"),
    ("bamboohr", "brightiron", "BrightIron"),
    ("bamboohr", "yempo", "Yempo"),
    ("recruitee", "wingmangroup", "Wingman Group"),
    ("teamtailor", "https://runremote-1694559579.teamtailor.com/jobs.json", "Run Remote"),
    ("workable", "virtual-staff-365", "Virtual Staff 365"),
    ("workable", "remote-raven", "Remote Raven"),
    ("workable", "pearltalent", "Pearl Talent"),
    ("workable", "treantly", "Treantly"),
    ("careerspage", "remote-employee-ph", "Remote Employee PH"),
    ("careerspage", "wizetalent", "WizeTalent"),
    ("breezy", "finstrat-management", "FinStrat Management"),
    ("breezy", "ourassistants", "OurAssistants"),
    ("breezy", "vadesk", "VA Desk"),
    ("lever", "assist-world", "Assist World"),
    ("zoho", "https://virtualcoworker.zohorecruit.com", "Virtual Coworker"),
    ("greenhouse", "extenteam", "Extenteam"),
    ("workable", "lago-1", "Lago"),
    ("workable", "profitcoach", "Profit Coach"),
    ("workable", "scalesource-1", "ScaleSource"),
    ("breezy", "value-virtual-assistants", "Value Virtual Assistants"),
    ("lever", "Sauce", "Sauce"),
    ("careerspage", "structure2scale-2", "Structure2Scale"),
    ("careerspage", "amz-allstars-ph", "AMZ Allstars PH"),
    ("zoho", "https://staffdomains.zohorecruit.com", "Staff Domain"),
    ("zoho", "https://peoplepartnersbpo.zohorecruit.com", "PeoplePartners"),
    ("zoho", "https://offshore247.zohorecruit.com", "Offshore 247"),
    ("zoho", "https://24x7direct.zohorecruit.com", "24x7 Direct"),
    ("zoho", "https://bookstime.zohorecruit.com", "BooksTime"),
    ("zoho", "https://boothandpartners.zohorecruit.com", "Booth & Partners"),
    ("careerspage", "clear-admin-people", "Clear Admin People"),
    ("careerspage", "boomering", "Boomering"),
    ("workable", "eandd", "Elevate and Delegate"),
    ("workable", "hirehawk", "HireHawk"),
    ("teamtailor", "https://virtualteammate-1719208705.teamtailor.com/jobs.json", "Virtual Teammate"),
    ("greenhouse", "crisprecruit", "Crisp Recruit"),
    ("recruitee", "resourcefultalentgroup", "Resourceful Talent Group"),
]
NOT_REMOTE_TITLE = re.compile(r"hybrid|on-?site|office[- ]based|\bpool(ing)?\b|\(internal\)", re.I)
# firm pages carry company boilerplate mentioning bookkeeping/Xero, so judge these feeds by title alone
FIRM_FINANCE_TITLE = re.compile(r"bookkeep|accountant|accounting|\baccounts\b|payroll|\btax\b|finance (officer|assistant|administrator)"
                                r"|financial (analyst|controller|accountant)|controller|xero|audit|reconcil|\bbas\b", re.I)


def _html_text(html: str) -> str:
    return BeautifulSoup(html or "", "html.parser").get_text("\n", strip=True)


def _firm_job(company: str, title: str, url: str, text: str, date_raw: str, remote_flag: bool | None) -> dict | None:
    # accounting titles are kept as-is; legal/analyst titles are tagged so only true entry-level ones survive
    category = None if FIRM_FINANCE_TITLE.search(title or "") else role_category(title or "")
    if not title or NOT_REMOTE_TITLE.search(title) or not (FIRM_FINANCE_TITLE.search(title) or category):
        return None
    remote = remote_flag if remote_flag is not None else bool(
        re.search(r"\b(wfh|work[- ]from[- ]home|home[- ]?based|remote)\b", title, re.I)
        or any(re.search(p, text.lower()) for p in REMOTE_ROLE_PATTERNS))
    if not remote:
        return None
    return {
        "title": title,
        "company": company,
        "url": url,
        "location": "Philippines (Remote)",
        "date_raw": date_raw,
        "date": parse_date_fuzzy(date_raw) if date_raw else None,
        "description": text.replace("\n", " ")[:800],
        "full_description": text,
        "tags": [],
        "source": company,
        "careers_page": True,
        **({"category": category} if category else {}),
    }


def _firm_feed_jobs(kind: str, ref: str, company: str) -> list[dict]:
    out = []
    if kind == "workable":
        url = f"https://apply.workable.com/api/v1/widget/accounts/{ref}?details=true"
        data = {}
        # Workable refuses (429 or a non-JSON page) after a couple of rapid calls, so space them and back off
        for wait in (8, 20, 40):
            time.sleep(wait)
            resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code == 200:
                try:
                    data = resp.json()
                    break
                except ValueError:
                    pass
        else:
            print(f"  [Offshore firms/{company}] Workable refused the request after 3 tries; skipped this run")
        seen = set()
        for j in data.get("jobs", []):
            # the widget repeats a job once per location
            if j.get("shortcode") in seen or (j.get("country") or "Philippines") != "Philippines":
                continue
            seen.add(j.get("shortcode"))
            out.append(_firm_job(company, j.get("title", ""), j.get("url") or j.get("shortlink", ""),
                                 _html_text(j.get("description")), j.get("published_on") or j.get("created_at", ""),
                                 True if j.get("telecommuting") and not (j.get("city") or "").strip() else None))
    elif kind == "lever":
        for j in requests.get(f"https://api.lever.co/v0/postings/{ref}?mode=json", headers=_headers(), timeout=REQUEST_TIMEOUT).json():
            place = f"{j.get('country') or ''} {(j.get('categories') or {}).get('location') or ''}"
            if j.get("country") not in (None, "", "PH") and "philippines" not in place.lower():
                continue
            text = "\n".join(t for t in [j.get("descriptionPlain"), j.get("additionalPlain")] + [
                _html_text(l.get("content")) for l in j.get("lists") or []] if t)
            created = datetime.fromtimestamp(j["createdAt"] / 1000, timezone.utc).isoformat() if j.get("createdAt") else ""
            out.append(_firm_job(company, j.get("text", ""), j.get("hostedUrl", ""), text, created,
                                 True if j.get("workplaceType") == "remote" else None))
    elif kind == "breezy":
        # the Breezy feed has no description, so only postings it flags as remote in the Philippines are taken
        for j in requests.get(f"https://{ref}.breezy.hr/json", headers=_headers(), timeout=REQUEST_TIMEOUT).json():
            loc = j.get("location") or {}
            if not loc.get("is_remote") or (loc.get("country") or {}).get("id") != "PH":
                continue
            kind_of_work = (j.get("type") or {}).get("name", "") if isinstance(j.get("type"), dict) else ""
            out.append(_firm_job(company, j.get("name", ""), j.get("url", ""), f"{kind_of_work}. Remote, Philippines.",
                                 j.get("published_date", ""), True))
    elif kind == "bamboohr":
        base, headers = f"https://{ref}.bamboohr.com/careers", {**_headers(), "Accept": "application/json"}
        for j in requests.get(f"{base}/list", headers=headers, timeout=REQUEST_TIMEOUT).json().get("result", []):
            title = j.get("jobOpeningName", "")
            # the list has no description; only fetch the detail for Philippine postings with a relevant title
            if (j.get("atsLocation") or {}).get("country") != "Philippines" or not (FIRM_FINANCE_TITLE.search(title) or role_category(title)):
                continue
            detail = (requests.get(f"{base}/{j['id']}/detail", headers=headers, timeout=REQUEST_TIMEOUT).json().get("result") or {}).get("jobOpening") or {}
            out.append(_firm_job(company, title, f"{base}/{j['id']}", _html_text(detail.get("description")),
                                 detail.get("datePosted") or "", True if str(j.get("locationType")) == "1" else None))
    elif kind == "recruitee":
        for j in requests.get(f"https://{ref}.recruitee.com/api/offers", headers=_headers(), timeout=REQUEST_TIMEOUT).json().get("offers", []):
            if "philippines" not in f"{j.get('country') or ''} {j.get('location') or ''}".lower():
                continue
            text = _html_text(f"{j.get('description') or ''}\n{j.get('requirements') or ''}")
            out.append(_firm_job(company, j.get("title", ""), j.get("careers_url", ""), text,
                                 j.get("published_at") or j.get("created_at") or "", True if j.get("remote") else None))
    elif kind == "careerspage":
        url = f"https://www.careers-page.com/api/v1.0/c/{ref}/jobs/"
        while url:
            page = requests.get(url, headers={**_headers(), "Accept": "application/json"}, timeout=REQUEST_TIMEOUT).json()
            for j in page.get("results", []):
                # the city is the firm's office, so remote status has to come from the title or description
                if j.get("country") == "Philippines":
                    out.append(_firm_job(company, j.get("position_name", ""), f"https://www.careers-page.com/{ref}/job/{j.get('hash')}",
                                         _html_text(j.get("description")), "", None))
            url = page.get("next")
    elif kind == "greenhouse":
        data = requests.get(f"https://boards-api.greenhouse.io/v1/boards/{ref}/jobs?content=true", headers=_headers(), timeout=REQUEST_TIMEOUT).json()
        for j in data.get("jobs", []):
            if "philippines" in ((j.get("location") or {}).get("name") or "").lower():
                out.append(_firm_job(company, j.get("title", ""), j.get("absolute_url", ""), _html_text(html_unescape(j.get("content") or "")),
                                     j.get("first_published") or j.get("updated_at") or "", None))
    elif kind == "teamtailor":
        for j in requests.get(ref, headers=_headers(), timeout=REQUEST_TIMEOUT).json().get("items", []):
            out.append(_firm_job(company, j.get("title", ""), j.get("url", ""), _html_text(j.get("content_html")),
                                 j.get("date_published", ""), None))
    elif kind == "zoho":
        data = requests.get(f"{ref}/recruit/v2/public/Job_Openings?pagename=Careers", headers=_headers(),
                            timeout=REQUEST_TIMEOUT).json()
        for j in data.get("data", []):
            url = j.get("$url") or j.get("Job_Opening_Url") or ref
            out.append(_firm_job(company, j.get("Posting_Title", ""), url, _html_text(j.get("Job_Description")),
                                 j.get("Date_Opened", ""), True if str(j.get("Remote_Job")).lower() == "yes" else None))
    elif kind == "awsm":
        for j in requests.get(f"{ref}/wp-json/wp/v2/awsm_job_openings?per_page=50", headers=_headers(),
                              timeout=REQUEST_TIMEOUT).json():
            out.append(_firm_job(company, _html_text((j.get("title") or {}).get("rendered")), j.get("link", ""),
                                 _html_text((j.get("content") or {}).get("rendered")), j.get("date", ""), None))
    elif kind == "venturex":
        for j in requests.get(f"{ref}/data/jobs.json", headers=_headers(), timeout=REQUEST_TIMEOUT).json():
            if not j.get("listed", True) or "filled" in (j.get("type") or "").lower():
                continue
            # VentureX places Filipino staff remotely with New Zealand businesses
            out.append(_firm_job(company, j.get("title", ""), f"{ref}/jobs/{j.get('id')}",
                                 f"{j.get('type', '')}. {j.get('summary', '')} New Zealand business.", j.get("posted", ""), True))
    elif kind == "connectos":
        soup = BeautifulSoup(requests.get(ref, headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
        seen = set()
        for a in soup.find_all("a", href=re.compile(r"jid=\d+")):
            title = a.get_text(" ", strip=True)
            if a["href"] in seen or not title or title.lower().startswith("view job"):
                continue
            seen.add(a["href"])
            # the title carries market and setup, e.g. "AU Bookkeeper (AU Accounting Firm, Homebased)"
            if not is_accounting_related(title, "") or NOT_REMOTE_TITLE.search(title):
                continue
            time.sleep(random.uniform(0.4, 0.9))
            page = BeautifulSoup(requests.get(a["href"], headers=_headers(), timeout=REQUEST_TIMEOUT).text, "html.parser")
            for tag in page(["script", "style", "nav", "header", "footer"]):
                tag.decompose()
            out.append(_firm_job(company, title, a["href"], page.get_text("\n", strip=True)[:8000], "", None))
    return [j for j in out if j]


def scrape_offshore_firms() -> list[dict]:
    jobs = []
    for kind, ref, company in OFFSHORE_FIRM_FEEDS:
        try:
            jobs.extend(_firm_feed_jobs(kind, ref, company))
        except Exception as e:
            print(f"  [Offshore firms/{company}] error: {e}")
    return jobs


# Offshore staffing firms whose careers boards run on Ashby (public posting API)
ASHBY_BOARDS = {
    "cas": "Cloud Accountant Staffing",
    "va4u": "VA4U",
    "decimal": "Decimal",
    "delplayagroup": "Del Playa Group",
}


def scrape_ashby_boards() -> list[dict]:
    """Careers boards of offshore accounting staffing firms hosted on Ashby."""
    jobs = []
    for board, company in ASHBY_BOARDS.items():
        try:
            resp = requests.get(f"https://api.ashbyhq.com/posting-api/job-board/{board}", headers=_headers(), timeout=REQUEST_TIMEOUT)
            if resp.status_code != 200:
                continue
            for item in resp.json().get("jobs", []):
                title = item.get("title", "")
                desc = item.get("descriptionPlain") or ""
                # firm pages mention bookkeeping in their boilerplate, so judge by title alone
                if not FIRM_FINANCE_TITLE.search(title):
                    continue
                locations = [item.get("location", "")] + [s.get("location", "") for s in item.get("secondaryLocations") or []]
                if not any("philippines" in (l or "").lower() for l in locations):
                    continue
                remote = item.get("isRemote") or (item.get("workplaceType") or "").lower() == "remote"
                emp = item.get("employmentType") or ""
                jobs.append({
                    "title": title,
                    "company": company,
                    "url": item.get("jobUrl", ""),
                    "location": "Philippines (Remote)" if remote else "Philippines",
                    "date_raw": item.get("publishedAt", ""),
                    "date": parse_date_fuzzy(item.get("publishedAt", "")),
                    "description": (f"{emp}. " if emp else "") + desc[:800],
                    "full_description": desc,
                    "tags": [emp] if emp else [],
                    "source": company,
                    "careers_page": True,
                })
        except Exception as e:
            print(f"  [Ashby/{board}] error: {e}")
    return jobs


# ── True entry-level detection (tax, legal & compliance, analyst) ───────
# A job only counts as entry-level if its FULL posting asks for no prior experience.
# Titles and short previews are not enough: many "Assistant" or "Junior" posts require 2+ years.

TAX_TITLE = re.compile(r"\btax(ation)?\b|\b1040\b", re.I)
# US tax roles (the user's stated goal). A tax title plus a US signal; 1040/1065/1120/990 and IRS are US-only forms.
US_TAX_SIGNAL = re.compile(r"\bu\.?s\.?\b|\bunited states\b|\bamerican\b|\birs\b|\b(?:form\s*)?(?:1040|1065|1120(?:-?s)?|990)\b", re.I)
NOT_TAX_JOB_TITLE = re.compile(r"executive (administrative )?assistant|\blaw\b|attorney|lawyer|immigration|strategist|advisor|planning", re.I)
LEGAL_TITLE = re.compile(
    r"paralegal|\blegal\b|law clerk|litigation|contracts? (review|reviewer|specialist|analyst|coordinator)|compliance"
    r"|\bkyc\b|\baml\b|anti[- ]money|immigration|conveyanc|e-?discovery|document review", re.I)
ANALYST_TITLE = re.compile(r"\banalyst\b|fp&a|\banalytics\b", re.I)
ANALYST_EXCLUDE = re.compile(
    r"\bseo\b|\bqa\b|quality|security|\bsoc\b|cyber|software|systems|\bit\b|network|marketing|social media|\bppc\b|\bsem\b"
    r"|\bcrm\b|salesforce|servicenow|\btest|game|clinical|medical|health|\bux\b|product|sales|ecommerce|amazon", re.I)
SENIOR_TITLE = re.compile(r"\b(senior|sr\.?|manager|lead|head|director|supervisor|reviewer|experienced|experts?|intermediate|controller|mid[- ]level)\b", re.I)
SUPPORT_TITLE = {
    "tax": re.compile(r"assistant|clerk|data entry|documentation|coordinator|support|\bva\b|trainee|junior|associate|staff", re.I),
    "legal": re.compile(r"legal assistant|legal secretary|legal (va|virtual)|virtual assistant|intake|clerk|document|records|admin|trainee|junior", re.I),
    "analyst": None,  # analyst roles must say they are entry-level; silence proves nothing
    "bookkeeping": None,  # a plain "Bookkeeper" proves nothing; needs an explicit entry signal in the posting
}
ENTRY_CATEGORY_LABEL = {"tax": "Tax", "legal": "Legal & compliance", "analyst": "Analyst",
                        "bookkeeping": "Bookkeeping & accounting"}
# Bookkeeping/accounting titles that are worth checking for genuine entry-level framing (no senior titles — those are
# screened out separately). The strict classifier still decides: it needs an explicit entry signal and no experience ask.
BOOKKEEPING_ENTRY_TITLE = re.compile(
    r"bookkeep\w*|account(?:s|ing|ant)?|accounts (payable|receivable)|\bap/ar\b|reconciliation|finance (assistant|clerk)", re.I)

ENTRY_SIGNALS = [
    ("says entry-level", r"entry[- ]level"),
    ("fresh graduates welcome", r"fresh (grad|graduate)s?|recent (grad|graduate)s?|graduate program|newly (licensed|passed)|board passers?|new(ly)? (licensed )?cpas?\b"),
    ("law students/graduates welcome", r"law (students?|graduates?)|suit (a |an )?(recent |fresh |law )?graduate|bar review(ee|er)s?"),
    ("no experience required", r"(?<!have )no (prior |previous |relevant )?(tax |legal |work )?experience (is )?(required|needed|necessary)|experience (is )?not (required|necessary)|no experience needed"),
    ("training provided", r"training (is |will be )?provided|we(?: will|'ll) train|willing to train|paid training|full training|on[- ]the[- ]job training"),
    ("junior/trainee role", r"\b(junior|trainee|apprentice|internship)\b"),
    ("0-2 years experience", r"\b0\s*(?:-|–|to)\s*[12]\s*years?|less than (?:1|one) year"),
]
SOFT_LINE = re.compile(
    r"\bpreferred\b|\bpreference\b|\bprefer\b|a plus\b|\bplus\b|advantage|\basset\b|nice to have|ideally|bonus|desirable|not required|not necessary|willing(ness)? to learn|\bif you have\b"
    r"|\bno (prior |previous |relevant )?(u\.?s\.? |au |australian )?(tax |legal |work )?experience\b|without (prior )?experience"
    r"|\b(gain|build|develop|grow)\b[^.]{0,30}\bexperience"
    r"|\b(tell us|describe|share (your|with us)|include (a|your)|in your (application|cover letter)|to apply|when applying|how to apply)\b", re.I)
SOFT_HEADER = re.compile(r"^\W*(preferred|nice[- ]to[- ]have|bonus|good to have|desirable|plus(es)?|preferred (skills|qualifications)|to apply|how to apply|application (requirements|instructions)|please (send|submit|include|provide)|when applying|in your application)\b", re.I)
HARD_HEADER = re.compile(r"^\W*(required|requirements?|qualifications?|mandatory|must[- ]haves?|what we(?:'re| are) looking for|who we want|about you|you have)\b", re.I)
NUM_WORDS = {"one": "1", "two": "2", "three": "3", "four": "4", "five": "5", "six": "6", "seven": "7", "eight": "8", "nine": "9", "ten": "10"}
YEARS_REQ = re.compile(r"(?:at least|minimum(?: of)?|min\.?|over)?\s*(\d{1,2})\s*\+?\s*(?:\(\d{1,2}\)\s*)?(?:-|–|to)?\s*(?:\d{1,2}\s*)?\+?\s*(?:years?|yrs?)\b", re.I)
DOMAIN = {
    "tax": r"tax|taxation|1040|1065|1120|return preparation|returns?",
    "legal": r"legal|law\b|law firm|paralegal|litigation|contracts?|compliance|kyc|aml|immigration|court|conveyanc|personal injury|estate planning|case management|e-?discovery",
    "analyst": r"analy\w*|financial|finance|fp&a|modell?ing|data|sql|power bi|tableau|reporting|research|credit|risk|compliance|kyc|aml|audit|accounting",
    "bookkeeping": r"bookkeep\w*|accounting|accounts|accountant|reconcil\w*|ledger|payroll|accounts payable|accounts receivable|ap/ar|quickbooks|xero|myob|month-end",
}
EXPERIENCED_TEAM = re.compile(r"experienced (team|professionals?|attorneys?|lawyers?|staff|seniors?|colleagues|mentors?|tax professional|accountants?|cpas?|analysts?|paralegals?)", re.I)


def _prior_experience_strength(line: str, category: str) -> str | None:
    """"hard" = an explicit experience requirement; "soft" = unquantified familiarity with the domain
    ("experience with reconciliations"), which a posting that also advertises itself as entry-level
    (training provided, junior, 0-2 years) should be allowed to override; None = no experience ask."""
    dom = DOMAIN[category]
    if re.search(r"\b(prior|previous|proven|relevant|demonstrated|substantial)\s+(?:[\w.-]+\s+){0,4}experience\b", line):
        return "hard"
    if re.search(r"\bmust (have|possess)\b[^.]{0,40}\bexperience\b|\bexperience (is )?(required|a must|mandatory|essential)\b", line):
        return "hard"
    if re.search(r"\b(hands-on|solid|strong)\b.{0,45}\b(" + dom + r")\b.{0,30}\bexperience", line):
        return "hard"
    if re.search(r"\bexperience (?:in|with|preparing|doing|as|handling|working|supporting)\b.{0,35}\b(" + dom + r")\b", line):
        return "soft"
    if re.search(r"\bexperienced\b.{0,30}\b(" + dom + r")", line) and not EXPERIENCED_TEAM.search(line):
        return "soft"
    return None


def _jobstreet_full_text(job_id: str) -> str:
    import uuid
    query = (
        'query jobDetails($jobId: ID!) { jobDetails(id: $jobId, tracking: {channel: "WEB", '
        f'jobDetailsViewedCorrelationId: "{uuid.uuid4()}", sessionId: "{uuid.uuid4()}"}}) '
        "{ job { content(platform: WEB) } } }"
    )
    headers = {**_headers(), "Content-Type": "application/json", "Origin": "https://ph.jobstreet.com",
               "Referer": "https://ph.jobstreet.com/", "seek-request-brand": "jobstreet", "seek-request-country": "PH"}
    resp = requests.post("https://ph.jobstreet.com/graphql", json={"operationName": "jobDetails", "query": query,
                         "variables": {"jobId": job_id}}, headers=headers, timeout=REQUEST_TIMEOUT)
    job = (((resp.json().get("data") or {}).get("jobDetails") or {}).get("job") or {})
    return BeautifulSoup(job.get("content") or "", "html.parser").get_text("\n", strip=True)


def _onlinejobs_full_text(url: str) -> str:
    resp = requests.get(url, headers=_headers(), timeout=REQUEST_TIMEOUT)
    if resp.status_code != 200:
        return ""
    soup = BeautifulSoup(resp.content, "html.parser")
    for tag in soup(["script", "style", "nav", "header", "footer"]):
        tag.decompose()
    text = soup.get_text("\n", strip=True)
    start = text.find("JOB OVERVIEW")
    text = text[start if start >= 0 else 0:]
    # Trim trailing page furniture. The "Required Application Questions" block lists multiple-choice answer
    # options like "3-5 years / 5+ years" that otherwise read as a fake experience requirement.
    for marker in ["Required Application Questions", "SKILL REQUIREMENT", "VIEW OTHER JOBS", "Share This Post"]:
        cut = text.find(marker)
        if cut > 0:
            text = text[:cut]
    return text[:10000]


def fetch_full_description(j: dict) -> str:
    try:
        source = j.get("source", "")
        if source == "Jobstreet PH":
            m = re.search(r"/job/(\d+)", j.get("url", ""))
            if m:
                return _jobstreet_full_text(m.group(1))
        elif source == "OnlineJobs.ph":
            return _onlinejobs_full_text(j["url"])
        elif source == "LinkedIn":
            return _linkedin_fetch_description(j["url"], max_chars=None)
    except Exception as e:
        print(f"  [full text/{j.get('source')}] error: {e}")
    return j.get("full_description") or j.get("description") or ""


def _posting_lines(title: str, full_text: str):
    # split sentences only after real words so abbreviations like "U.S." stay intact
    for raw in re.split(r"[\n•●▪◦;]|(?<=[a-z]{2}[.!?])\s+", f"{title}\n{full_text}"):
        line = re.sub(r"\bor (an )?equivalent (work )?experience\b", "", raw.strip(), flags=re.I)
        line = re.sub(r"\b(one|two|three|four|five|six|seven|eight|nine|ten)\b(?=\s*(\(\d+\)\s*)?\+?\s*(years?|yrs))",
                      lambda m: NUM_WORDS[m.group(1).lower()], line, flags=re.I)
        if line:
            yield line


def _requirement_clauses(title: str, full_text: str):
    """Yield the clauses of a posting that state hard requirements (case preserved).
    Skips "Preferred"/application sections and optional clauses like "X is a plus"."""
    mode_soft = False
    for line in _posting_lines(title, full_text):
        if SOFT_HEADER.search(line):
            mode_soft = True
            continue
        if HARD_HEADER.search(line):
            mode_soft = False
        if mode_soft:
            continue
        if not SOFT_LINE.search(line):
            yield line
            continue
        # "X, Y and Z preferred" is all optional; "X preferred, 3+ years Y" still requires Y;
        # "3+ years X, ideally within Y" softens only the "ideally ..." part
        parts = re.split(r",|\s[-–]\s", line)
        qualifier = re.compile(r"^\s*(ideally|preferably|particularly|especially|such as|e\.g\.|including|with a preference)\b", re.I)
        if all(qualifier.search(p) or not SOFT_LINE.search(p) for p in parts):
            yield from (p for p in parts if not qualifier.search(p))
            continue
        first_soft = next(i for i, p in enumerate(parts) if SOFT_LINE.search(p) or i == len(parts) - 1)
        yield from (p for i, p in enumerate(parts) if i > first_soft and not SOFT_LINE.search(p))


def classify_entry_level(title: str, full_text: str, category: str = "tax") -> tuple[bool, str]:
    """Return (is_genuine_entry_level, reason). Rejects on any hard experience requirement."""
    entry_hits = []
    for line in _posting_lines(title, full_text):
        low = line.lower()
        for label, pat in ENTRY_SIGNALS:
            if re.search(pat, low) and label not in entry_hits:
                entry_hits.append(label)
    # strong, explicit entry-level signals that let a role override a soft "experience with X" familiarity line
    STRONG_ENTRY = {"says entry-level", "no experience required", "training provided",
                    "0-2 years experience", "junior/trainee role", "fresh graduates welcome"}
    has_strong = any(h in STRONG_ENTRY for h in entry_hits)
    for clause in _requirement_clauses(title, full_text):
        low = clause.lower()
        m = YEARS_REQ.search(low)
        # >15 years is company history ("with 75 years of experience, our focus..."), not a job requirement
        if m and 1 <= int(m.group(1)) <= 15 \
                and re.search(r"experience|\+\s*(years?|yrs?)|\b(years?|yrs?) (?:of|in|doing|with|working|as)\b", low) \
                and not re.search(r"\b(since|founded|in business|serving)\b", low):
            return False, f"requires {m.group(1)}+ years: {clause.strip()[:90]}"
        strength = _prior_experience_strength(low, category)
        if strength == "hard" or (strength == "soft" and not has_strong):
            return False, f"requires prior experience: {clause.strip()[:90]}"
    if entry_hits:
        return True, ", ".join(entry_hits)
    support = SUPPORT_TITLE.get(category)
    if support and support.search(title) \
            and not re.search(r"accountant|bookkeeper|preparer|\bcpa\b|analyst", title, re.I):
        return True, "support role, no experience requirement in the full posting"
    return False, "no entry-level signal"


# US bookkeeping/accounting/tax experience the user does not have. Case-sensitive "US" so the pronoun "us" never matches;
# "US-based firm" describes the employer, not the experience asked for. 1040/1065/1120/990 and IRS only exist in US tax.
US_EXPERIENCE = re.compile(
    r"(?:\bU\.?S\.?A?\b|\bUnited States\b|\bAmerican\b)(?![- ]based)[\s,/&()-]{0,3}(?:[\w.-]+[\s,/&()-]+){0,2}?"
    r"(?i:bookkeep\w*|accounting|accountant|clients?|small business\w*|GAAP|companies|firms?|entities|CPA firm|tax\w*|returns?)"
    r"|(?i:bookkeep\w*|accounting|tax (?:preparation|prep|returns?|compliance))\s+(?i:for|with|in|of)\s+(?:[\w.-]+\s+){0,2}?(?:U\.?S\.?A?\b|United States|American)"
    r"|\b(?:Form\s*)?(?:1040|1065|1120(?:-?S)?|990)\b|\bIRS\b"
    # "supporting a US-based company" is experience asked of the candidate, unlike "our US-based firm"
    r"|(?i:supporting|serving|with|for|working (?:with|for))\s+(?:an?\s+|the\s+)?(?:U\.?S\.?|US)[- ]based\s+(?i:compan|client|business|firm|entit|organi)")
US_EXP_MIN_YEARS = 2
# Experience tied to another country (AU, NZ, UK, ...): the user can meet up to 2 years, so 3+ is out.
LOCAL_EXPERIENCE = re.compile(
    r"(?:\b(?:Australian?|New Zealand|Kiwi|United Kingdom|British|Canadian?|Singapore(?:an)?|Hong Kong|Irish|Ireland|UAE|Dubai|Saudi|European)\b"
    r"|\b(?:AU|NZ|UK|EU|ANZ|AUS)\b)(?![- ]based)[\s,/&()-]{0,3}(?:[\w.'-]+[\s,/&()-]+){0,3}?"
    r"(?i:bookkeep\w*|accounting|accountant|clients?|small business\w*|compan\w*|firms?|entit\w*|practice|tax\w*|returns?"
    r"|payroll|compliance|legislation|law|legal|conveyancing|mortgage|lending|market|environment|standards|business\w*|smes?"
    r"|superannuation|industry|experience|smsf)"
    r"|(?i:experience|background|bookkeep\w*|accounting|work(?:ing|ed)?)\s+(?i:in|with|within|for|at|of|supporting)\s+(?:an?\s+|the\s+)?"
    r"(?:[\w.'-]+\s+){0,2}?(?:Australia\w*|New Zealand|NZ|AU|UK|United Kingdom|Canada|Canadian|Singapore)\b"
    r"|\b(?:ATO|BAS|SMSF|IRD|HMRC|CRA)\b")
LOCAL_EXP_MIN_YEARS = 3


def _year_phrases(clause: str):
    """Yield (min_years, phrase) for each "N years ..." in a clause. The phrase runs through the experience noun it
    governs ("5+ years of dedicated, end-to-end Australian payroll experience") and then stops at the next comma, so
    "3+ years of accounting experience, knowledge of Australian tax" does not tie the 3 years to Australia."""
    stops = r"[,;)]|(?<=[a-z]{2})\.\s+[A-Z]"
    for m in YEARS_REQ.finditer(clause):
        n = int(m.group(1))
        if not 1 <= n <= 15:
            continue
        start = max(clause.rfind(d, 0, m.start()) for d in ",;(•") + 1
        rest = clause[m.end():]
        noun = re.search(r"experience|background|expertise", rest[:70], re.I)
        hard = re.search(r"[;)]|(?<=[a-z]{2})\.\s+[A-Z]", rest)
        cut = noun.end() if noun and (not hard or noun.start() < hard.start()) else 0
        tail = re.search(stops, rest[cut:])
        yield n, clause[start:m.end() + cut + (tail.start() if tail else len(rest) - cut)]


def country_experience_required(title: str, full_text: str) -> str | None:
    """Return the requirement if the posting needs 2+ years of US or 3+ years of other country-specific experience."""
    for clause in _requirement_clauses(title, full_text):
        for n, phrase in _year_phrases(clause):
            if n >= US_EXP_MIN_YEARS and US_EXPERIENCE.search(phrase):
                return phrase.strip()[:110]
            if n >= LOCAL_EXP_MIN_YEARS and LOCAL_EXPERIENCE.search(phrase):
                return phrase.strip()[:110]
    return None


def role_category(title: str) -> str | None:
    if is_licensed_legal_role(title):
        return None
    if LEGAL_TITLE.search(title):
        return "legal"
    if ANALYST_TITLE.search(title) and not ANALYST_EXCLUDE.search(title):
        return "analyst"
    return None


ENTRY_ROLE_QUERIES = [
    "paralegal", "junior paralegal", "legal assistant", "legal researcher", "legal virtual assistant",
    "law clerk", "compliance analyst", "kyc analyst", "contract reviewer",
    "junior financial analyst", "financial analyst", "junior data analyst", "data analyst",
    "business analyst", "research analyst", "fp&a analyst", "credit analyst", "junior analyst",
]
ENTRY_ROLE_QUERIES_INDEED = ["paralegal", "legal assistant", "compliance analyst", "junior financial analyst", "data analyst", "junior analyst"]


def scrape_entry_roles() -> list[dict]:
    """Legal/compliance and analyst roles; only genuine entry-level ones survive mark_entry_level()."""
    accept = lambda title, desc: role_category(title) is not None
    jobs, searches = [], []
    for fn, queries in [(scrape_jobstreet_ph, ENTRY_ROLE_QUERIES), (scrape_onlinejobs_ph, ENTRY_ROLE_QUERIES),
                        (scrape_workable, ENTRY_ROLE_QUERIES), (scrape_jobspy, ENTRY_ROLE_QUERIES_INDEED),
                        (scrape_jobgether, ["paralegal", "legal-assistant", "compliance", "financial-analyst", "data-analyst"]),
                        (scrape_builtin, ["paralegal", "legal assistant", "compliance analyst", "financial analyst", "junior analyst"]),
                        (scrape_4dayweek, ["paralegal", "legal assistant", "compliance", "financial analyst", "data analyst"]),
                        (scrape_remote_com, ["paralegal", "legal assistant", "analyst"]),
                        (scrape_remotefirstjobs, ["paralegal philippines", "legal assistant philippines"]),
                        (scrape_bruntwork, ["all"]),
                        (scrape_somewhere, ["paralegal", "legal assistant", "analyst"])]:
        searches.append((fn, queries))

    def run_search(search):
        fn, queries = search
        try:
            return fn(queries=queries, accept=accept)
        except Exception as e:
            print(f"  [Entry roles/{fn.__name__}] error: {e}")
            return []

    with ThreadPoolExecutor(max_workers=len(searches)) as pool:
        for results in pool.map(run_search, searches):
            for j in results:
                j["category"] = role_category(j["title"])
                jobs.append(j)
    return jobs


# ── Working hours ───────────────────────────────────────────────────────
# The user cannot work full-time between noon and 10 PM Philippine time (part-time is fine at any hour).
BLOCKED_PH_HOURS = (12, 22)
BLOCKED_MIN_SHARE = 0.5   # a shift conflicts when at least this share of it falls inside the blocked window

# (label, UTC offset in standard time, pattern). Uppercase abbreviations only; "PST (Philippine...)" and "GMT+8"
# are Philippine time, and Canada's "GST/HST" tax is not Hawaii time.
_CLOCK = r"(?:[AaPp]\.?[Mm]\.?|\d)\s*\(?"
WORK_ZONES = [
    ("Philippine time", 8, r"Philippine (?:[Ss]tandard )?[Tt]ime|\bPHS?T\b|Manila [Tt]ime|\bPH [Tt]ime|PST\s*\(?(?:Philippine|Manila|PH\b)|(?:GMT|UTC)\s?\+\s?8"),
    ("Hawaii time", -10, r"[Hh]awaii|Honolulu|" + _CLOCK + r"HST\b"),
    ("Pacific time", -8, r"[Pp]acific (?:[Ss]tandard |[Dd]aylight )?[Tt]ime|\bPST\b|\bPDT\b|" + _CLOCK + r"PT\b"),
    ("Mountain time", -7, r"[Mm]ountain (?:[Ss]tandard )?[Tt]ime|\bMST\b|\bMDT\b"),
    ("Central time", -6, r"[Cc]entral (?:[Ss]tandard )?[Tt]ime|\bCST\b|\bCDT\b"),
    ("Eastern time", -5, r"[Ee]astern (?:[Ss]tandard |[Dd]aylight )?[Tt]ime|\bEST\b|\bEDT\b|" + _CLOCK + r"ET\b"),
    ("UK time", 0, r"\bUK (?:time|hours|shift|business hours|working hours)|\bGMT\b(?!\s?[+-])|\bBST\b|London [Tt]ime|British [Tt]ime"),
    ("Central European time", 1, r"\bCES?T\b|European (?:time|hours|business hours)|Central European [Tt]ime"),
    ("UAE time", 4, r"Dubai [Tt]ime|UAE [Tt]ime|Gulf Standard [Tt]ime"),
    ("India time", 5.5, r"\bIST\b|Indian? (?:Standard )?[Tt]ime"),
    ("Singapore/Hong Kong time", 8, r"\bSGT\b|\bHKT\b|Singapore (?:[Tt]ime|hours)|Hong Kong (?:[Tt]ime|hours)"),
    ("Perth time", 8, r"\bAWST\b|Perth [Tt]ime"),
    ("Australian Eastern time", 10, r"\bAE[SD]T\b|(?:Sydney|Melbourne|Brisbane) [Tt]ime|Australian (?:Eastern )?(?:Standard |Daylight )?[Tt]ime"
                                   r"|(?:AU|Australian) (?:business |working |office )?hours|(?:AU|Australian) [Dd]ay ?[Ss]hift|\bAU [Tt]ime"),
    ("New Zealand time", 12, r"\bNZ[SD]T\b|(?:New Zealand|NZ) (?:[Tt]ime|business hours|working hours|hours)"),
]
# zones whose ordinary business day sits inside the blocked window even when the posting gives no clock times
ASSUME_DAY_SHIFT_BLOCKED = {"UK time", "Central European time", "UAE time", "India time", "Singapore/Hong Kong time", "Perth time"}
SHIFT_RANGE = re.compile(
    r"(\d{1,2})(?::(\d{2}))?\s*(?:([AaPp])\.?\s?[Mm]\.?)?\s*(?:-|–|—|to|until|till)\s*(\d{1,2})(?::(\d{2}))?\s*([AaPp])\.?\s?[Mm]\b\.?")


def _clock(hour: str, minute: str | None, meridiem: str) -> float:
    return int(hour) % 12 + (12 if meridiem.lower() == "p" else 0) + int(minute or 0) / 60


def _fmt_hour(h: float) -> str:
    h %= 24
    whole, minutes = int(h), round((h % 1) * 60)
    return f"{whole % 12 or 12}{f':{minutes:02d}' if minutes else ''} {'AM' if whole < 12 else 'PM'}"


def job_shift(text: str) -> dict | None:
    """The working hours a posting asks for, in Philippine time: {label, start, hours, explicit}.
    Uses a stated clock range and its time zone when present, else a 9-to-5 day in the first zone named."""
    zones = sorted((m.start(), i, label, offset) for i, (label, offset, pat) in enumerate(WORK_ZONES) for m in re.finditer(pat, text))
    for m in SHIFT_RANGE.finditer(text):
        h1, m1, mer1, h2, m2, mer2 = m.groups()
        if int(h1) > 12 or int(h2) > 12:
            continue
        end = _clock(h2, m2, mer2)
        # "8-5pm" means 8 AM; "1-9pm" means 1 PM
        if not mer1:
            mer1 = "a" if mer2.lower() == "p" and int(h1) % 12 > int(h2) % 12 else mer2
        start = _clock(h1, m1, mer1)
        hours = (end - start) % 24
        if not 3 <= hours <= 14:
            continue
        near = [z for z in zones if m.start() - 90 <= z[0] <= m.end() + 90]
        if near:
            _, _, label, offset = min(near, key=lambda z: (abs(z[0] - m.end()), z[1]))
        elif len({z[2] for z in zones}) == 1:
            _, _, label, offset = zones[0]
        else:
            continue
        return {"label": label, "start": (start + 8 - offset) % 24, "hours": hours, "explicit": True}
    if zones:
        _, _, label, offset = zones[0]
        return {"label": label, "start": (9 + 8 - offset) % 24, "hours": 8, "explicit": False}
    if re.search(r"\bmid[- ]?shift\b", text, re.I):
        return {"label": "Mid shift", "start": 14, "hours": 9, "explicit": False}
    return None


def blocked_share(shift: dict) -> float:
    """Share of the shift (sampled every 15 minutes) that falls inside the blocked Philippine-time window."""
    steps = max(1, int(shift["hours"] * 4))
    inside = sum(1 for i in range(steps) if BLOCKED_PH_HOURS[0] <= (shift["start"] + i / 4) % 24 < BLOCKED_PH_HOURS[1])
    return inside / steps


def is_part_time(j: dict) -> bool:
    head = f"{j['title']} {' '.join(j.get('tags') or [])} {j.get('description', '')[:400]}"
    if re.search(r"part[- ]?time", head, re.I):
        return True
    text = f"{head} {(j.get('_full_text') or j.get('full_description') or '')[:3000]}"
    m = re.search(r"(\d{1,2})\s*(?:[-–]\s*(\d{1,2})\s*)?(?:hours?|hrs?)\s*(?:per|a|/|each)\s*week", text, re.I)
    return bool(m and int(m.group(2) or m.group(1)) <= 30)


def exclude_blocked_hours(jobs: list[dict]) -> list[dict]:
    """Label each job's hours in Philippine time and drop full-time jobs that fall in the blocked window."""
    kept, dropped = [], []
    for j in jobs:
        text = f"{j['title']} {j.get('_full_text') or j.get('full_description') or j.get('description', '')}"
        shift = job_shift(text)
        if shift:
            j["_tz"] = shift["label"]
            j["_tz_hours"] = (f"about {_fmt_hour(shift['start'])} to {_fmt_hour(shift['start'] + shift['hours'])} in the Philippines"
                              + ("" if shift["explicit"] else " (assuming a 9-to-5 day)"))
            certain = shift["explicit"] or shift["label"] in ASSUME_DAY_SHIFT_BLOCKED or shift["label"] == "Mid shift"
            if certain and blocked_share(shift) >= BLOCKED_MIN_SHARE and not is_part_time(j):
                dropped.append(j)
                continue
        kept.append(j)
    print(f"Excluded {len(dropped)} full-time jobs whose hours fall in {_fmt_hour(BLOCKED_PH_HOURS[0])} to {_fmt_hour(BLOCKED_PH_HOURS[1])} Philippine time")
    for j in dropped[:25]:
        print(f"    - {j['title'][:55]} :: {j['_tz']}, {j['_tz_hours']}")
    return kept


# Employer review ratings (overall / work-life-balance out of 5) for the larger recruiters that recur in this market
# and actually have a review footprint. Small firms (most of the market) have none, so those keep the keyword estimate.
# Hand-curated from Glassdoor/Indeed; ratings drift slowly, so refresh every few months. Source noted per entry.
EMPLOYER_REVIEWS_RAW = [
    (["TOA Global", "TOA"], {"rating": 3.9, "wlb": 4.1, "n": 54, "src": "Glassdoor"}),
    (["BruntWork"], {"rating": 4.9, "wlb": 4.8, "n": 1373, "src": "Glassdoor/Indeed"}),
    (["Staff Domain", "Staff Domain Inc"], {"rating": 4.6, "wlb": 4.6, "n": 183, "src": "Glassdoor"}),
    (["Virtual Coworker"], {"rating": 4.3, "wlb": 3.8, "n": 7, "src": "Glassdoor/Indeed"}),
    (["Outsourced", "Outsourced.ph"], {"rating": 4.2, "wlb": 4.8, "n": 29, "src": "Indeed"}),
    (["Cloudstaff"], {"rating": 4.2, "wlb": 4.3, "n": 258, "src": "Indeed"}),
    (["MicroSourcing"], {"rating": 4.0, "wlb": 4.1, "n": 197, "src": "Glassdoor/Indeed"}),
    (["Booth & Partners", "Booth and Partners", "Booth"], {"rating": 3.5, "wlb": 4.0, "n": 157, "src": "Glassdoor/Indeed"}),
    (["Sourcefit", "Sourcefit Philippines"], {"rating": 3.5, "wlb": 4.3, "n": 107, "src": "Glassdoor/Indeed"}),
    (["Somewhere", "Shepherd"], {"rating": 4.5, "wlb": None, "n": None, "src": "Trustpilot"}),
]


def _norm_employer(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", (name or "").lower())


EMPLOYER_REVIEWS = {_norm_employer(alias): data for aliases, data in EMPLOYER_REVIEWS_RAW for alias in aliases}


def enrich_employer_reviews(jobs: list[dict]) -> None:
    """Attach real Glassdoor/Indeed ratings to jobs whose employer (company or source) is a known larger recruiter.
    Everything else keeps the keyword-based workload estimate -- most small firms have no review footprint to verify."""
    matched = 0
    for j in jobs:
        for name in (j.get("company"), j.get("source")):
            data = EMPLOYER_REVIEWS.get(_norm_employer(name))
            if data:
                j["_employer_rating"] = data["rating"]
                j["_employer_wlb"] = data["wlb"]
                j["_employer_reviews_n"] = data["n"]
                j["_employer_src"] = data["src"]
                matched += 1
                break
    print(f"Employer review ratings matched: {matched} jobs")


def mark_us_tax(jobs: list[dict]) -> None:
    """Flag US tax roles (the user's goal). These survived the experience filter, so they don't demand the
    2+ years of US tax experience the user lacks -- the ones actually worth applying to."""
    for j in jobs:
        title = j["title"]
        if not (TAX_TITLE.search(title) and not NOT_TAX_JOB_TITLE.search(title)):
            continue
        text = f"{title} {get_full_text(j) or j.get('description', '')}"
        if US_TAX_SIGNAL.search(text):
            j["_us_tax"] = True
    print(f"US tax roles: {sum(1 for j in jobs if j.get('_us_tax'))} jobs")


# AU/NZ bookkeeping -- the user's fastest-hire fit (CPA + EY AU/NZ audit + Xero NZ Payroll).
AUNZ_SIGNAL = re.compile(r"\baustralia\b|australian|\bnew zealand\b|\bnz\b|\bbas\b|\bato\b|\bird\b|smsf|myob|smartly", re.I)
AUNZ_CORE = re.compile(r"xero|bookkeep|account", re.I)


def mark_aunz(jobs: list[dict]) -> None:
    """Flag AU/NZ Xero/bookkeeping roles -- the user's strongest, fastest-hire fit."""
    for j in jobs:
        if SENIOR_TITLE.search(j["title"]):
            continue
        text = f"{j['title']} {get_full_text(j) or j.get('description', '')}"
        if AUNZ_SIGNAL.search(text) and AUNZ_CORE.search(text):
            j["_aunz"] = True
    print(f"AU/NZ bookkeeping roles: {sum(1 for j in jobs if j.get('_aunz'))} jobs")


# Legal support roles a law student can do (and that build legal experience). Attorney/lawyer roles need a
# license the user doesn't have yet, so they're excluded.
LEGAL_LANE_TITLE = re.compile(
    r"paralegal|legal (assistant|secretary|va|virtual|admin|support|intake|operations?|research\w*|clerk|coordinator)"
    r"|litigation support|document review|conveyanc|legal ops|compliance (assistant|support)", re.I)
ATTORNEY_TITLE = re.compile(r"\battorney\b|\blawyer\b|solicitor|barrister|\besq\b|general counsel", re.I)


def mark_legal(jobs: list[dict]) -> None:
    """Flag legal support / paralegal roles -- a law-student lane. Surviving legal-category roles are already
    restricted to lane-appropriate titles by mark_entry_level."""
    for j in jobs:
        if j.get("category") == "legal" or j.get("_entry_category") == "legal":
            j["_legal"] = True
    print(f"Legal (law-student lane) roles: {sum(1 for j in jobs if j.get('_legal'))} jobs")


def mark_high_pay(jobs: list[dict]) -> None:
    """Flag jobs whose stated pay can reach HIGH_PAY_MIN_USD a month (top of the range)."""
    for j in jobs:
        # a bookkeeping/accounting title is required; pay above the cap is usually a mislabelled currency
        if not FIRM_FINANCE_TITLE.search(j["title"]):
            continue
        rng = monthly_usd_range(j)
        if rng and HIGH_PAY_MIN_USD <= rng[1] <= HIGH_PAY_MAX_USD:
            j["_high_pay"], j["_pay_usd"] = True, [round(rng[0]), round(rng[1])]
    print(f"High pay (${HIGH_PAY_MIN_USD:,}+/month): {sum(1 for j in jobs if j.get('_high_pay'))} jobs")


def prefetch_full_texts(jobs: list[dict]) -> None:
    """Fetch full postings ahead of the entry-level and experience checks, two at a time per website."""
    def will_be_dropped(j):
        return j.get("category") in ("legal", "analyst") and SENIOR_TITLE.search(j["title"])

    by_source = {}
    for j in jobs:
        if j.get("source") in ("Jobstreet PH", "OnlineJobs.ph", "LinkedIn") and not will_be_dropped(j):
            by_source.setdefault(j["source"], []).append(j)
    lanes = [group[i::2] for group in by_source.values() for i in range(2)]
    with ThreadPoolExecutor(max_workers=max(1, len(lanes))) as pool:
        list(pool.map(lambda lane: [get_full_text(j) for j in lane], lanes))


def get_full_text(j: dict) -> str:
    """Full posting text, fetched once per job and cached on the dict."""
    if "_full_text" not in j:
        j["_full_text"] = fetch_full_description(j)
        if j.get("source") in ("Jobstreet PH", "OnlineJobs.ph", "LinkedIn"):
            time.sleep(random.uniform(0.4, 0.9))
    return j["_full_text"]


def exclude_country_experience_required(jobs: list[dict]) -> list[dict]:
    """Drop jobs needing 2+ years of US or 3+ years of other country-specific (AU, NZ, UK, ...) experience."""
    kept, dropped = [], []
    for j in jobs:
        why = country_experience_required(j["title"], get_full_text(j) or j.get("description", ""))
        (dropped if why else kept).append(j)
        if why:
            j["_us_exp_reason"] = why
    print(f"Excluded {len(dropped)} jobs requiring {US_EXP_MIN_YEARS}+ yrs US or {LOCAL_EXP_MIN_YEARS}+ yrs other country-specific experience")
    for j in dropped[:25]:
        print(f"    - {j['title'][:55]} :: {j['_us_exp_reason'][:80]}")
    return kept


def mark_entry_level(jobs: list[dict]) -> list[dict]:
    """Flag genuine entry-level jobs. Legal and analyst jobs that are not entry-level are dropped; tax and
    bookkeeping/accounting jobs are always kept (they just gain the _entry flag when the posting proves it)."""
    kept, checked = [], {"tax": 0, "legal": 0, "analyst": 0, "bookkeeping": 0}
    for j in jobs:
        title = j["title"]
        cat = j.get("category")
        if cat is None and TAX_TITLE.search(title) and not NOT_TAX_JOB_TITLE.search(title):
            cat = "tax"
        # Bookkeeping/accounting roles are the user's core target: check them for genuine entry-level framing too.
        if cat is None and BOOKKEEPING_ENTRY_TITLE.search(title):
            cat = "bookkeeping"
        if cat is None:
            kept.append(j)
            continue
        if not SENIOR_TITLE.search(title):
            checked[cat] += 1
            text = get_full_text(j)
            if cat == "analyst" and re.search(r"\b(maps? evaluator|search (engine )?evaluator|ads? evaluator|\brater\b|data annotat|data label)", text, re.I):
                j["_entry_reject"] = "rater/evaluator gig, not an analyst role"
                text = ""
            if len(text) >= 300:
                ok, reason = classify_entry_level(title, text, cat)
                if ok:
                    j["_entry"], j["_entry_reason"], j["_entry_category"] = True, reason, cat
                else:
                    j["_entry_reject"] = reason
        # law-student lane: keep legal support/paralegal roles even when they ask for some experience
        legal_lane = (cat == "legal" and LEGAL_LANE_TITLE.search(title)
                      and not SENIOR_TITLE.search(title) and not ATTORNEY_TITLE.search(title))
        if cat in ("tax", "bookkeeping") or j.get("_entry") or legal_lane:
            kept.append(j)
    found = {c: sum(1 for j in kept if j.get("_entry_category") == c) for c in checked}
    print("True entry-level: " + ", ".join(f"{ENTRY_CATEGORY_LABEL[c]} {found[c]}/{checked[c]}" for c in checked))
    return kept


# ── Pipeline ────────────────────────────────────────────────────────────

SCRAPERS = [
    ("RemoteOK", scrape_remoteok),
    ("Remotive", scrape_remotive),
    ("Jobicy", scrape_jobicy),
    ("Himalayas", scrape_himalayas),
    ("Arbeitnow", scrape_arbeitnow),
    ("LinkedIn", scrape_linkedin_rss),
    ("LinkedIn Posts", scrape_linkedin_posts),
    ("Jobstreet PH", scrape_jobstreet_ph),
    ("OnlineJobs.ph", scrape_onlinejobs_ph),
    ("Kalibrr", scrape_kalibrr),
    ("WorkingNomads", scrape_working_nomads),
    ("WeWorkRemotely", scrape_weworkremotely),
    ("Accountingfly", scrape_accountingfly),
    ("Indeed PH", scrape_jobspy),
    ("RemoteRocketship", scrape_remoterocketship),
    ("Hubstaff Talent", scrape_hubstaff_talent),
    ("VirtualStaff.ph", scrape_virtualstaff_ph),
    ("Workable", scrape_workable),
    ("Ashby boards", scrape_ashby_boards),
    ("TOA Global", scrape_toa_global),
    ("Jobgether", scrape_jobgether),
    ("Built In", scrape_builtin),
    ("AU/NZ offshore firms", scrape_offshore_firms),
    ("4 Day Week", scrape_4dayweek),
    ("Remote.com", scrape_remote_com),
    ("CaribbeanJobs", scrape_caribbeanjobs),
    ("RemoteFirstJobs", scrape_remotefirstjobs),
    ("BruntWork", scrape_bruntwork),
    ("Somewhere", scrape_somewhere),
    ("jobdataapi", scrape_jobdataapi),
    ("Jobsora PH", scrape_jobsora),
    ("Entry-level legal & analyst", scrape_entry_roles),
]


def deduplicate(jobs: list[dict]) -> list[dict]:
    seen_ids = set()
    by_posting = {}
    unique = []
    for j in jobs:
        jid = job_id(j["title"], j["company"], j["url"])
        if jid in seen_ids:
            continue
        seen_ids.add(jid)
        # Same posting syndicated to several boards: merge on title + company when the company is known
        company = re.sub(r"[^a-z0-9]", "", (j.get("company") or "").lower())
        if company:
            key = (re.sub(r"[^a-z0-9]", "", j["title"].lower()), company)
            kept = by_posting.get(key)
            if kept:
                if not kept.get("salary") and j.get("salary"):
                    kept["salary"] = j["salary"]
                if len(j.get("description") or "") > len(kept.get("description") or ""):
                    kept["description"] = j["description"]
                # a syndicated copy may carry the posting date the kept one lacks
                if not kept.get("date") and j.get("date"):
                    kept["date"], kept["date_raw"] = j["date"], j.get("date_raw", "")
                continue
        entry = {**j, "_id": jid}
        if company:
            by_posting[key] = entry
        unique.append(entry)
    return unique


def filter_jobs(jobs: list[dict]) -> list[dict]:
    cutoff = datetime.now(timezone.utc) - timedelta(days=MAX_AGE_DAYS)
    niche_cutoff = datetime.now(timezone.utc) - timedelta(days=NICHE_MAX_AGE_DAYS)
    filtered = []
    for j in jobs:
        if is_excluded(j["title"], j["description"], j.get("location", "")):
            continue
        if not is_confirmed_remote(j):
            continue
        # drop dead listings whose page says the role is gone
        if re.search(r"no job found|no longer available|position (has been )?filled|job (has )?expired|posting (has )?expired",
                     f"{j['title']} {j.get('description', '')}", re.I):
            continue
        if j["date"] and j["date"].tzinfo is None:
            j["date"] = j["date"].replace(tzinfo=timezone.utc)
        if j["date"]:
            longer = j.get("careers_page") or NICHE_PATTERN.search(f"{j['title']} {j['description']}".lower())
            if j["date"] < (niche_cutoff if longer else cutoff):
                continue
        else:
            # no date even after backfill: can't confirm it's within the freshness window, so exclude it
            continue
        j["_score"] = relevance_score(j["title"], j["description"], j.get("location", ""))
        j["_prob"] = acceptance_probability(j["title"], j["description"], j.get("location", ""), j.get("tags"))
        j["_busy"], j["_busy_label"] = busyness_rating(j["title"], j["description"])
        filtered.append(j)
    return filtered


FLEX_KEYWORDS = [
    "flexible", "flex schedule", "flexible hours", "flexible schedule",
    "flexible work", "flexible time", "flexible working",
    "own hours", "set your own", "choose your hours", "choose your own hours",
    "work at your own pace", "at your own pace", "anytime",
    "work when you want", "async", "asynchronous",
    "no fixed schedule", "no set hours", "no set schedule",
]
PT_KEYWORDS = [
    "part-time", "part time", "parttime",
    "20 hours", "25 hours", "15 hours", "10 hours",
    "20hrs", "25hrs", "15hrs", "10hrs",
    "half time", "half-time",
    "few hours a week", "hours per week",
    "contract", "freelance", "project-based", "project based",
    "casual", "per diem",
]


def _is_flex_or_pt(j: dict) -> bool:
    text = f"{j.get('title','')} {j.get('description','')} {j.get('salary','')} {' '.join(j.get('tags',[]))}".lower()
    return any(k in text for k in FLEX_KEYWORDS + PT_KEYWORDS)


def sort_jobs(jobs: list[dict]) -> list[dict]:
    """Highest chance of getting accepted first (Fit %), with flexible/part-time given a strong lift
    (the user balances law study), then freshest."""
    def sort_key(j):
        prob = j.get("_prob", 40)
        flex_bonus = 12 if _is_flex_or_pt(j) else 0  # surface flexible/part-time well up the list
        dt = j.get("date")
        has_date = 0 if dt is None else 1
        dt = dt or datetime.min.replace(tzinfo=timezone.utc)
        return (prob + flex_bonus, has_date, dt, j.get("_score", 0))
    return sorted(jobs, key=sort_key, reverse=True)


# ── HTML Report ─────────────────────────────────────────────────────────

def _render_row(j: dict, new_ids: set[str], section: str = "") -> str:
    is_new = j["_id"] in new_ids
    new_badge = '<span class="badge new">NEW</span>' if is_new else ""
    entry_html = ""
    if j.get("_entry"):
        reason = html_escape(j.get("_entry_reason", ""))
        cat = ENTRY_CATEGORY_LABEL.get(j.get("_entry_category"), "")
        entry_html = f'<div class="entry-reason"><span class="badge entry-cat">{cat}</span> Why entry-level: {reason}</div>'
    if j.get("_tz"):
        entry_html += f'<div class="tz-note">{j["_tz"]}: {j["_tz_hours"]}</div>'
    if j.get("_high_pay"):
        lo, hi = j["_pay_usd"]
        usd = f"${lo:,}" if lo == hi else f"${lo:,} to ${hi:,}"
        entry_html += f'<div class="high-pay">About {usd} a month</div>'
    score = j.get("_score", 0)
    if score >= 10:
        match_class = "match-high"
        match_label = "Strong match"
    elif score >= 5:
        match_class = "match-med"
        match_label = "Good match"
    else:
        match_class = "match-low"
        match_label = "Worth a look"

    text_lower = f"{j['title']} {j['description']} {j.get('salary','')} {' '.join(j.get('tags',[]))}".lower()
    flex_badge = ""
    if any(k in text_lower for k in FLEX_KEYWORDS):
        flex_badge = '<span class="badge flex">Flexible hours</span> '
    pt_badge = ""
    if any(k in text_lower for k in PT_KEYWORDS):
        pt_badge = '<span class="badge pt">Part-time</span> '

    tags_html = ""
    if j.get("tags"):
        tag_items = [f"<span class='tag'>{t}</span>" for t in j["tags"][:5]]
        tags_html = " ".join(tag_items)

    desc_preview = j["description"][:200].replace("<", "&lt;")
    if len(j["description"]) > 200:
        desc_preview += "..."

    pay = extract_pay(f"{j['title']} {j['description']}")
    salary = j.get("salary", "")
    pay_display = pay or salary or ""
    normalized = normalize_pay(pay_display)
    if pay_display and normalized and normalized != pay_display:
        pay_html = f'<span class="pay">{pay_display}</span><br><small class="pay-norm">{normalized}</small>'
    elif pay_display:
        pay_html = f'<span class="pay">{pay_display}</span>'
    else:
        pay_html = '<span class="pay muted">--</span>'

    prob = j.get("_prob", 40)
    if prob >= 70:
        prob_class = "prob-high"
    elif prob >= 50:
        prob_class = "prob-med"
    else:
        prob_class = "prob-low"

    busy = j.get("_busy", 3)
    busy_label = j.get("_busy_label", "Moderate")
    busy_dots = "&#9679;" * busy + '<span style="opacity:0.2">' + "&#9679;" * (5 - busy) + "</span>"
    busy_classes = {1: "busy-light", 2: "busy-easy", 3: "busy-mod", 4: "busy-busy", 5: "busy-heavy"}
    busy_class = busy_classes.get(busy, "busy-mod")

    # Real employer rating when the company is a known larger recruiter; otherwise just the keyword estimate.
    emp_html = ""
    if j.get("_employer_rating"):
        wlb = f" &middot; WLB {j['_employer_wlb']:.1f}" if j.get("_employer_wlb") else ""
        n = j.get("_employer_reviews_n")
        tip = f"{j.get('_employer_src', '')} {j['_employer_rating']:.1f}/5 overall" + (f", {n} reviews" if n else "")
        emp_html = f"<br><small class='emp-rating' title='{tip}'>&#9733; {j['_employer_rating']:.1f}{wlb}</small>"

    is_flex = bool(flex_badge or pt_badge)
    row_classes = []
    if is_new:
        row_classes.append("new-row")
    if is_flex:
        row_classes.append("flex-row")

    jid = html_escape(str(j.get("_id", "")))
    search_blob = html_escape(f"{j['title']} {j.get('company', '')} {j['source']}".lower())
    src_attr = html_escape(j["source"])
    date_sort = int(j["date"].timestamp()) if j.get("date") else 0  # epoch so the Posted column sorts chronologically
    return f"""
    <tr class="{' '.join(row_classes)}" data-id="{jid}" data-fit="{prob}" data-source="{src_attr}" data-section="{section}" data-search="{search_blob}">
        <td class="freshness" data-sort="{date_sort}">{freshness_label(j['date'])}</td>
        <td>
            <a href="{j['url']}" target="_blank" class="job-title">{j['title']}</a>
            {new_badge}
            <div class="company">{j['company']}</div>
            <div style="margin-top:3px">{flex_badge}{pt_badge}</div>
            {entry_html}
            <div class="desc">{desc_preview}</div>
            {tags_html}
            <div class="rowctl"><button type="button" class="ctl ctl-applied" onclick="jobMark('{jid}','applied')">&#10003; applied</button><button type="button" class="ctl ctl-hide" onclick="jobMark('{jid}','hidden')">&#10005; hide</button></div>
        </td>
        <td>{j['location']}</td>
        <td>{pay_html}</td>
        <td data-sort="{prob}"><span class="badge {prob_class}">{prob}%</span></td>
        <td><span class="{busy_class}" title="{busy_label}">{busy_dots}</span><br><small class="busy-label">{busy_label}</small>{emp_html}</td>
        <td><span class="badge {match_class}">{match_label}</span></td>
        <td class="source">{j['source']}</td>
    </tr>"""


def render_html(jobs: list[dict], new_ids: set[str], stats: dict) -> str:
    today = datetime.now().strftime("%A, %B %d, %Y")
    # Your apply-list: the two target types (US tax + AU/NZ bookkeeping), surfaced at the very top.
    def in_applylist(j):
        return j.get("_us_tax") or j.get("_aunz") or j.get("_legal")
    apply_rows = [_render_row(j, new_ids, "apply-list") for j in jobs if in_applylist(j)]
    entry_rows = [_render_row(j, new_ids, "entry-level") for j in jobs if j.get("_entry") and not in_applylist(j)]
    high_jobs = sorted((j for j in jobs if j.get("_high_pay") and not j.get("_entry") and not in_applylist(j)),
                       key=lambda j: j["_pay_usd"], reverse=True)
    high_rows = [_render_row(j, new_ids, "high-pay") for j in high_jobs]
    rows = [_render_row(j, new_ids, "other") for j in jobs
            if not j.get("_entry") and not in_applylist(j) and not j.get("_high_pay")]

    source_summary = ", ".join(
        f"{name}: {count}" for name, count in sorted(stats["per_source"].items())
    )

    # Excel-style controls: live search, min-Fit, source/section filters, applied/hide marks, sortable columns.
    controls_html = """
<div class="controls">
  <input id="f-search" type="text" placeholder="Search title, company or source…" oninput="applyFilters()">
  <label class="fctl">Min Fit <input id="f-fit" type="number" min="0" max="100" value="0" oninput="applyFilters()">%</label>
  <select id="f-source" onchange="applyFilters()"><option value="">All sources</option></select>
  <select id="f-section" onchange="applyFilters()">
    <option value="">All sections</option>
    <option value="apply-list">Apply-list</option>
    <option value="entry-level">Entry-level</option>
    <option value="high-pay">High pay</option>
    <option value="other">Other</option>
  </select>
  <label class="fctl"><input id="f-hideapplied" type="checkbox" onchange="applyFilters()"> Hide applied/hidden</label>
  <button type="button" class="ctl" onclick="resetMarks()">Reset marks</button>
  <span id="f-count" class="fcount"></span>
</div>
<div class="hint">Tip: click a column header to sort. Mark rows &#10003; applied or &#10005; hide &mdash; marks persist on this device.</div>"""

    filter_js = """
<script>
const MARK_KEY = 'jobScraperMarks';
function loadMarks(){ try { return JSON.parse(localStorage.getItem(MARK_KEY) || '{}'); } catch(e){ return {}; } }
function saveMarks(m){ try { localStorage.setItem(MARK_KEY, JSON.stringify(m)); } catch(e){} }
let marks = loadMarks();
function jobMark(id, state){
  if (marks[id] === state) { delete marks[id]; } else { marks[id] = state; }
  saveMarks(marks); applyFilters();
}
function resetMarks(){ marks = {}; saveMarks(marks); applyFilters(); }
function applyFilters(){
  const q = (document.getElementById('f-search').value || '').toLowerCase().trim();
  const minFit = parseInt(document.getElementById('f-fit').value || '0', 10) || 0;
  const src = document.getElementById('f-source').value;
  const sec = document.getElementById('f-section').value;
  const hideMarked = document.getElementById('f-hideapplied').checked;
  let shown = 0;
  document.querySelectorAll('tr[data-id]').forEach(function(tr){
    const id = tr.getAttribute('data-id');
    const mark = marks[id];
    tr.classList.toggle('row-applied', mark === 'applied');
    tr.classList.toggle('row-hidden', mark === 'hidden');
    let ok = true;
    if (q && (tr.getAttribute('data-search') || '').indexOf(q) === -1) ok = false;
    if (ok && (parseInt(tr.getAttribute('data-fit') || '0', 10) < minFit)) ok = false;
    if (ok && src && tr.getAttribute('data-source') !== src) ok = false;
    if (ok && sec && tr.getAttribute('data-section') !== sec) ok = false;
    if (ok && hideMarked && mark) ok = false;
    tr.style.display = ok ? '' : 'none';
    if (ok) shown++;
  });
  const c = document.getElementById('f-count');
  if (c) c.textContent = shown + ' shown';
}
function initSources(){
  const sel = document.getElementById('f-source');
  const set = new Set();
  document.querySelectorAll('tr[data-id]').forEach(function(tr){ set.add(tr.getAttribute('data-source')); });
  Array.from(set).filter(Boolean).sort().forEach(function(s){
    const o = document.createElement('option'); o.value = s; o.textContent = s; sel.appendChild(o);
  });
}
function cellVal(tr, i){
  const td = tr.children[i]; if (!td) return '';
  const ds = td.getAttribute('data-sort'); if (ds !== null) return parseFloat(ds);
  const t = td.textContent.trim();
  const n = parseFloat(t.replace(/[^0-9.\\-]/g, ''));
  return isNaN(n) ? t.toLowerCase() : n;
}
function initSort(){
  document.querySelectorAll('table').forEach(function(table){
    const ths = table.querySelectorAll('thead th');
    ths.forEach(function(th, idx){
      th.style.cursor = 'pointer'; th.title = 'Click to sort';
      let asc = false;
      th.addEventListener('click', function(){
        asc = !asc;
        const tbody = table.querySelector('tbody');
        const rows = Array.from(tbody.querySelectorAll('tr[data-id]'));
        rows.sort(function(a,b){
          const va = cellVal(a, idx), vb = cellVal(b, idx);
          if (va < vb) return asc ? -1 : 1;
          if (va > vb) return asc ? 1 : -1;
          return 0;
        });
        rows.forEach(function(r){ tbody.appendChild(r); });
      });
    });
  });
}
document.addEventListener('DOMContentLoaded', function(){ initSources(); initSort(); applyFilters(); });
</script>"""

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Job Scraper Report - {today}</title>
<style>
:root {{
    --bg: #0f172a;
    --surface: #1e293b;
    --border: #334155;
    --text: #e2e8f0;
    --text-muted: #94a3b8;
    --accent: #38bdf8;
    --green: #4ade80;
    --yellow: #facc15;
    --red: #f87171;
}}
* {{ margin: 0; padding: 0; box-sizing: border-box; }}
body {{
    font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
    background: var(--bg);
    color: var(--text);
    padding: 24px;
    line-height: 1.5;
}}
.header {{
    display: flex;
    justify-content: space-between;
    align-items: baseline;
    margin-bottom: 16px;
    flex-wrap: wrap;
    gap: 8px;
}}
h1 {{ font-size: 1.4rem; font-weight: 600; }}
.subtitle {{ color: var(--text-muted); font-size: 0.85rem; }}
.stats {{
    display: flex;
    gap: 16px;
    margin-bottom: 20px;
    flex-wrap: wrap;
}}
.stat-card {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 12px 20px;
    min-width: 120px;
}}
.stat-card .num {{ font-size: 1.6rem; font-weight: 700; color: var(--accent); }}
.stat-card .label {{ font-size: 0.75rem; color: var(--text-muted); text-transform: uppercase; letter-spacing: 0.05em; }}
table {{
    width: 100%;
    border-collapse: collapse;
    background: var(--surface);
    border-radius: 8px;
    overflow: hidden;
}}
th {{
    background: #0f172a;
    padding: 10px 14px;
    text-align: left;
    font-size: 0.75rem;
    text-transform: uppercase;
    letter-spacing: 0.05em;
    color: var(--text-muted);
    border-bottom: 1px solid var(--border);
}}
td {{
    padding: 12px 14px;
    border-bottom: 1px solid var(--border);
    font-size: 0.88rem;
    vertical-align: top;
}}
tr:last-child td {{ border-bottom: none; }}
tr:hover {{ background: rgba(56, 189, 248, 0.05); }}
tr.new-row {{ background: rgba(74, 222, 128, 0.06); }}
tr.flex-row {{ border-left: 3px solid #c084fc; background: rgba(168, 85, 247, 0.07); }}
tr.flex-row td:first-child {{ padding-left: 10px; }}
.job-title {{
    color: var(--accent);
    text-decoration: none;
    font-weight: 600;
}}
.job-title:hover {{ text-decoration: underline; }}
.company {{ color: var(--text-muted); font-size: 0.8rem; margin-top: 2px; }}
.desc {{ color: var(--text-muted); font-size: 0.78rem; margin-top: 4px; max-width: 500px; }}
.freshness {{ white-space: nowrap; font-weight: 600; font-size: 0.85rem; }}
.source {{ color: var(--text-muted); font-size: 0.8rem; white-space: nowrap; }}
.pay {{ font-size: 0.82rem; font-weight: 500; color: var(--green); white-space: nowrap; }}
.pay.muted {{ color: var(--text-muted); font-weight: 400; }}
.badge {{
    display: inline-block;
    padding: 2px 8px;
    border-radius: 12px;
    font-size: 0.7rem;
    font-weight: 600;
    text-transform: uppercase;
    letter-spacing: 0.03em;
}}
.badge.new {{ background: var(--green); color: #000; margin-left: 6px; }}
.badge.match-high {{ background: rgba(74,222,128,0.15); color: var(--green); }}
.badge.match-med {{ background: rgba(250,204,21,0.15); color: var(--yellow); }}
.badge.match-low {{ background: rgba(148,163,184,0.15); color: var(--text-muted); }}
.badge.prob-high {{ background: rgba(74,222,128,0.2); color: #4ade80; font-weight: 700; }}
.badge.prob-med {{ background: rgba(250,204,21,0.2); color: #facc15; }}
.badge.prob-low {{ background: rgba(148,163,184,0.15); color: var(--text-muted); }}
.busy-light {{ color: #4ade80; letter-spacing: 2px; }}
.busy-easy {{ color: #86efac; letter-spacing: 2px; }}
.busy-mod {{ color: #facc15; letter-spacing: 2px; }}
.busy-busy {{ color: #fb923c; letter-spacing: 2px; }}
.busy-heavy {{ color: #f87171; letter-spacing: 2px; }}
.busy-label {{ color: var(--text-muted); font-size: 0.7rem; }}
.pay-norm {{ color: #4ade80; font-size: 0.75rem; font-weight: 600; }}
.badge.flex {{ background: rgba(168,85,247,0.2); color: #c084fc; }}
.badge.pt {{ background: rgba(56,189,248,0.15); color: var(--accent); }}
.tag {{
    display: inline-block;
    background: rgba(56,189,248,0.1);
    color: var(--accent);
    padding: 1px 6px;
    border-radius: 4px;
    font-size: 0.7rem;
    margin-top: 4px;
    margin-right: 4px;
}}
.empty {{
    text-align: center;
    padding: 60px 20px;
    color: var(--text-muted);
}}
.section-title {{ font-size: 1.05rem; margin: 22px 0 6px; color: var(--text); }}
.section-count {{ font-size: 0.8rem; color: var(--text-muted); font-weight: 400; margin-left: 6px; }}
.section-note {{ font-size: 0.8rem; color: var(--text-muted); margin-bottom: 8px; }}
.entry-table {{ border: 1px solid rgba(52, 211, 153, 0.35); }}
.entry-reason {{ font-size: 0.78rem; color: #34d399; margin-top: 3px; }}
.badge.entry-cat {{ background: rgba(52, 211, 153, 0.15); color: #34d399; }}
.empty.small {{ padding: 16px; }}
.ustax-table {{ border: 1px solid rgba(96, 165, 250, 0.45); }}
.emp-rating {{ color: #fbbf24; font-size: 0.72rem; white-space: nowrap; }}
.controls {{ display: flex; flex-wrap: wrap; gap: 8px; align-items: center; background: var(--surface); border: 1px solid var(--border); border-radius: 8px; padding: 10px 12px; margin-bottom: 6px; position: sticky; top: 0; z-index: 5; }}
.controls input[type=text] {{ flex: 1 1 220px; min-width: 160px; background: var(--bg); color: var(--text); border: 1px solid var(--border); border-radius: 6px; padding: 7px 10px; font-size: 0.85rem; }}
.controls input[type=number] {{ width: 54px; background: var(--bg); color: var(--text); border: 1px solid var(--border); border-radius: 6px; padding: 5px 6px; margin: 0 4px; }}
.controls select {{ background: var(--bg); color: var(--text); border: 1px solid var(--border); border-radius: 6px; padding: 6px 8px; font-size: 0.85rem; }}
.controls .fctl {{ font-size: 0.8rem; color: var(--text-muted); display: inline-flex; align-items: center; }}
.fcount {{ font-size: 0.8rem; color: var(--accent); margin-left: auto; font-weight: 600; }}
.hint {{ font-size: 0.75rem; color: var(--text-muted); margin-bottom: 14px; }}
.ctl {{ background: var(--bg); color: var(--text-muted); border: 1px solid var(--border); border-radius: 5px; padding: 5px 9px; font-size: 0.75rem; cursor: pointer; }}
.ctl:hover {{ color: var(--text); border-color: var(--accent); }}
.rowctl {{ margin-top: 6px; display: flex; gap: 6px; }}
.ctl-applied:hover {{ color: var(--green); border-color: var(--green); }}
.ctl-hide:hover {{ color: var(--red); border-color: var(--red); }}
tr.row-applied {{ opacity: 0.55; }}
tr.row-applied .job-title::after {{ content: " \\2713"; color: var(--green); }}
tr.row-hidden {{ opacity: 0.4; }}
th {{ user-select: none; }}
.high-table {{ border: 1px solid rgba(251, 191, 36, 0.4); }}
.high-pay {{ font-size: 0.78rem; color: #fbbf24; margin-top: 3px; }}
.tz-note {{ font-size: 0.78rem; color: #7dd3fc; margin-top: 3px; }}
.footer {{
    margin-top: 16px;
    font-size: 0.75rem;
    color: var(--text-muted);
    text-align: center;
}}
</style>
</head>
<body>
<div class="header">
    <h1>Bookkeeper Job Scraper</h1>
    <div class="subtitle">{today} &middot; Sources: {source_summary}</div>
</div>
<div class="stats">
    <div class="stat-card"><div class="num">{stats['total']}</div><div class="label">Total jobs</div></div>
    <div class="stat-card"><div class="num">{stats['new']}</div><div class="label">New today</div></div>
    <div class="stat-card"><div class="num">{stats['strong']}</div><div class="label">Strong match</div></div>
</div>
{controls_html}
<h2 class="section-title">&#127919; Your apply-list: US tax + AU/NZ + legal (apply this week) <span class="section-count">{len(apply_rows)}</span></h2>
<div class="section-note">Your target role types, surfaced together &mdash; <strong>US tax</strong> postings that don't require US experience you lack, <strong>AU/NZ Xero/bookkeeping</strong> (your fastest-hire fit), and <strong>legal support / paralegal</strong> roles (a law-student lane). Flexible/part-time surfaced higher. Apply within 1&ndash;2 days; match the CV to the role.</div>
{"<table class='ustax-table'><thead><tr><th>Posted</th><th>Job</th><th>Location</th><th>Pay</th><th>Fit %</th><th>Workload</th><th>Match</th><th>Source</th></tr></thead><tbody>" + "".join(apply_rows) + "</tbody></table>" if apply_rows else '<div class="empty small">No US tax or AU/NZ roles cleared the filters today.</div>'}
<h2 class="section-title">&#11088; Easiest to get hired: genuine entry-level <span class="section-count">{len(entry_rows)}</span></h2>
<div class="section-note">Your highest-chance roles &mdash; bookkeeping, accounting, tax, legal &amp; analyst postings whose full text asks for <em>no prior experience</em> (training provided, junior/trainee, or 0&ndash;2 years). Highest Fit %% first. Each row says why it qualified.</div>
{"<table class='entry-table'><thead><tr><th>Posted</th><th>Job</th><th>Location</th><th>Pay</th><th>Fit %</th><th>Workload</th><th>Match</th><th>Source</th></tr></thead><tbody>" + "".join(entry_rows) + "</tbody></table>" if entry_rows else '<div class="empty small">No genuine entry-level roles today.</div>'}
<h2 class="section-title">High pay: ${HIGH_PAY_MIN_USD:,}+ a month <span class="section-count">{len(high_rows)}</span></h2>
<div class="section-note">Remote roles you can apply to from the Philippines whose stated pay can reach ${HIGH_PAY_MIN_USD:,} a month, highest first. Hourly rates assume full-time unless the posting gives weekly hours.</div>
{"<table class='high-table'><thead><tr><th>Posted</th><th>Job</th><th>Location</th><th>Pay</th><th>Fit %</th><th>Workload</th><th>Match</th><th>Source</th></tr></thead><tbody>" + "".join(high_rows) + "</tbody></table>" if high_rows else '<div class="empty small">No jobs with stated pay at this level today.</div>'}
<h2 class="section-title">All other jobs <span class="section-count">{len(rows)}</span></h2>
{"<table><thead><tr><th>Posted</th><th>Job</th><th>Location</th><th>Pay</th><th>Fit %</th><th>Workload</th><th>Match</th><th>Source</th></tr></thead><tbody>" + "".join(rows) + "</tbody></table>" if rows else '<div class="empty">No matching jobs found today. The scraper will check again tomorrow.</div>'}
<div class="footer">Sorted by Fit %% (your estimated chance of getting accepted) first, then flexible/part-time, then newest. Fit %% weighs skill match, eligibility and competition; Match score weighs Xero, NZ/AU, part-time and bookkeeping keywords.</div>
{filter_js}
</body>
</html>"""


# ── Main ────────────────────────────────────────────────────────────────

def main():
    REPORT_DIR.mkdir(exist_ok=True)
    seen = load_seen()
    all_jobs = []

    print(f"Scraping {len(SCRAPERS)} sources...")
    HEADERS.update(_headers())

    def run_source(entry):
        name, fn = entry
        try:
            return fn()
        except Exception as e:
            print(f"  [{name}] failed: {e}")
            return []

    # sources are different websites, so they run side by side; each scraper still paces its own requests
    with ThreadPoolExecutor(max_workers=10) as pool:
        for (name, _), results in zip(SCRAPERS, pool.map(run_source, SCRAPERS)):
            print(f"  [{name}] {len(results)} jobs")
            all_jobs.extend(results)

    print(f"\nRaw results: {len(all_jobs)}")

    jobs = deduplicate(all_jobs)
    print(f"After dedup:  {len(jobs)}")

    backfill_dates(jobs)

    jobs = filter_jobs(jobs)
    print(f"After filter: {len(jobs)}")

    prefetch_full_texts(jobs)
    jobs = mark_entry_level(jobs)
    jobs = exclude_country_experience_required(jobs)
    jobs = exclude_blocked_hours(jobs)
    mark_us_tax(jobs)
    mark_aunz(jobs)
    mark_legal(jobs)
    mark_high_pay(jobs)
    enrich_employer_reviews(jobs)
    jobs = sort_jobs(jobs)

    new_ids = set()
    for j in jobs:
        if j["_id"] not in seen:
            new_ids.add(j["_id"])
            seen[j["_id"]] = {
                "title": j["title"],
                "first_seen": datetime.now(timezone.utc).isoformat(),
            }

    per_source = {}
    for j in jobs:
        per_source[j["source"]] = per_source.get(j["source"], 0) + 1
    strong = sum(1 for j in jobs if j.get("_score", 0) >= 10)

    stats = {
        "total": len(jobs),
        "new": len(new_ids),
        "strong": strong,
        "per_source": per_source,
    }

    html = render_html(jobs, new_ids, stats)
    report_path = REPORT_DIR / f"jobs_{datetime.now().strftime('%Y-%m-%d')}.html"
    report_path.write_text(html)
    # machine-readable copy (incl. full posting text) for follow-up questions about today's jobs
    export = [{**{k: v for k, v in j.items() if k != "date"}, "date": j["date"].isoformat() if j.get("date") else None,
               "full_text": j.get("_full_text") or j.get("full_description") or j.get("description", "")} for j in jobs]
    report_path.with_suffix(".json").write_text(json.dumps(export, default=str, ensure_ascii=False))
    save_seen(seen)

    print(f"\nReport: {report_path}")
    print(f"  Total: {stats['total']}  New: {stats['new']}  Strong match: {stats['strong']}")

    if "--no-open" not in sys.argv:
        webbrowser.open(f"file://{report_path.resolve()}")


if __name__ == "__main__":
    main()
