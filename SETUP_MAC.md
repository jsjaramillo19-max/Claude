# Running the job scraper on your Mac

Running it locally (instead of in the cloud session) has two big wins:
- **The Workable offshore-firm boards work** (Hunt St, Twoconnect, Manila Recruitment, etc.) — they're no longer rate-limited, because you're not behind a shared proxy IP.
- **It can run itself every morning** via macOS `launchd`.

Everything below is a one-time setup. After that, a fresh report lands daily on its own.

---

## 1. Get the code (one time)

Open **Terminal** and run:

```bash
# Install Homebrew if you don't have it (skip if you do):
# /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"

brew install python git          # skip any you already have
cd ~                             # or wherever you want the project
git clone https://github.com/jsjaramillo19-max/claude.git Claude
cd Claude
git checkout claude/zealous-lovelace-9yo3zl   # the branch with the latest scraper + setup files
```

> Tip: once you're happy with it, you can merge this branch into `main` on GitHub so future clones don't need the `git checkout` line.

## 2. Install dependencies (one time)

```bash
chmod +x setup_mac.sh run_daily.sh
./setup_mac.sh
```

This creates a self-contained `.venv` folder and installs everything. It won't touch your system Python.

## 3. Test it

```bash
./run_daily.sh
```

It scrapes, writes `job_reports/jobs_YYYY-MM-DD.html`, and opens it in your browser. First run takes a few minutes.

## 4. Schedule it daily (one time)

1. Find your project's full path:
   ```bash
   pwd
   ```
   Copy the result (e.g. `/Users/john/Claude`).

2. Edit `com.jobscraper.daily.plist` and replace `/Users/CHANGE_ME/Claude` with that path (two spots: the `run_daily.sh` line). Change the `Hour`/`Minute` if you want a time other than 7:00 AM.

3. Install and start the schedule:
   ```bash
   cp com.jobscraper.daily.plist ~/Library/LaunchAgents/
   launchctl load ~/Library/LaunchAgents/com.jobscraper.daily.plist
   ```

That's it — it now runs every day at your chosen time.

### Managing the schedule

```bash
# Run it right now to test the schedule:
launchctl start com.jobscraper.daily

# Stop/remove the daily schedule:
launchctl unload ~/Library/LaunchAgents/com.jobscraper.daily.plist

# After editing the .plist, reload it:
launchctl unload ~/Library/LaunchAgents/com.jobscraper.daily.plist
cp com.jobscraper.daily.plist ~/Library/LaunchAgents/
launchctl load ~/Library/LaunchAgents/com.jobscraper.daily.plist

# Logs if something looks off:
cat /tmp/jobscraper.out.log
cat /tmp/jobscraper.err.log
```

## Keeping the scraper up to date

When the scraper code changes, refresh your copy:

```bash
cd ~/Claude
git pull
./setup_mac.sh      # only needed if requirements.txt changed
```

## Notes

- The Mac must be **awake** at the scheduled time (or it runs when it next wakes, if it was asleep). If it's fully shut down, it runs at the next scheduled time it's on.
- Reports and run state (`job_reports/`) stay local and are git-ignored.
- To run manually any time: `cd ~/Claude && ./run_daily.sh`.
