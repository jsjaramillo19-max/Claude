#!/usr/bin/env bash
# One-time setup for running the job scraper on macOS.
# Creates a local Python virtual environment and installs dependencies.
set -euo pipefail
cd "$(dirname "$0")"

if ! command -v python3 >/dev/null 2>&1; then
  echo "Python 3 not found. Install it first:  brew install python"
  echo "(If you don't have Homebrew: https://brew.sh)"
  exit 1
fi

echo "Creating virtual environment (.venv)…"
python3 -m venv .venv
source .venv/bin/activate
python3 -m pip install --upgrade pip >/dev/null
echo "Installing dependencies…"
python3 -m pip install -r requirements.txt

echo ""
echo "Setup complete. Test it now with:  ./run_daily.sh"
