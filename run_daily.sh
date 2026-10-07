#!/usr/bin/env bash
# Runs the job scraper and opens today's report. Safe to run manually or from launchd.
set -euo pipefail
cd "$(dirname "$0")"
source .venv/bin/activate

# Generate the report quietly (don't let the scraper try to open a browser itself).
python3 job_scraper.py --no-open

# Open the newest report in the default browser (works when you're logged in; ignored otherwise).
latest="$(ls -t job_reports/jobs_*.html 2>/dev/null | head -1 || true)"
if [ -n "${latest}" ]; then
  open "${latest}" 2>/dev/null || true
  echo "Opened: ${latest}"
fi
