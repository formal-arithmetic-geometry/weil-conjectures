#!/usr/bin/env python3
"""History of the quality metrics, for the quality dashboard (`dashboard/`).

The history is a directory (on the `quality-data` branch, under `data/`) with two files:

  history.jsonl   one JSON object per line and per recorded master commit, sorted by date:
                    {"schema": 1, "commit": SHA, "date": "YYYY-MM-DDTHH:MM:SSZ", "source": ...,
                     "metrics": {KIND: {SERIES: number}},
                     "kernel": {"rev": SHA, "threshold_ms": T, "top": [[ms, module, decl], ...]}}
                  `date` is the commit's committer date (UTC); `source` is "backfill" or "daily";
                  `kernel` (the slowest declarations) is present only when a kernel table was
                  measured for that commit.
  meta.json       {"schema": 1, "title": ..., "repo_url": ..., "updated": ...,
                   "kinds": [{"id", "label", "group", "description", "unit", "lower_is_better",
                              "max_series"}]}
                  the metadata of each metric kind, in display order.

A *kind* is one chart: a set of named series in one unit (e.g. `debt.limits`, with one series per
option and direction). Within a record, a kind that is present but lacks a series means 0 for that
series (the counters omit zeros); a kind that is absent means "not measured" (a gap in the chart).
The page renders every kind it finds in the records, with the metadata from meta.json when there
is any; so a new metric is a new key under "metrics" (and, ideally, an entry in KINDS below).

Commands:
  history.py backfill --data DIR [--ref REF] [--since YYYY-MM-DD | --days N] [--repo-url URL]
      Record one commit per UTC day (the last first-parent commit of REF on that day). The
      counters are read from git objects (no checkout) and updated incrementally from one
      sampled commit to the next: only the files that differ are re-read.
  history.py update --data DIR --rev REV [--kernel TABLE] [--repo-url URL] [--max-gap-days N]
      Record REV (replacing an earlier record of the same commit), with the kernel table's
      statistics when given, after filling the days missed since the last record (as backfill).

Only git objects and the given files are read; the script runs no project code.
"""

import argparse
import datetime
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tech_debt"))
import metrics  # noqa: E402
import kernel_times  # noqa: E402

SCHEMA = 1
KERNEL_TOP = 25

# Metric kinds, in display order. Kinds without an entry here are still recorded and shown, with
# defaults derived from their id.
DEBT = "Technical debt"
KERNEL = "Kernel type-checking"
KINDS = [
    {"id": "debt.unfinished", "label": "sorry, admit and axioms", "group": DEBT, "unit": "occurrences",
     "lower_is_better": True,
     "description": "`sorry` and `admit` in code, and `axiom` declarations."},
    {"id": "debt.backward", "label": "Backward-compatibility options", "group": DEBT, "unit": "options",
     "lower_is_better": True,
     "description": "`set_option backward.* ...`, per option: strong technical debt in Mathlib's terms."},
    {"id": "debt.limits", "label": "Heartbeat and limit modifications", "group": DEBT, "unit": "options",
     "lower_is_better": True,
     "description": "`maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxRecDepth` and "
                    "`synthInstance.maxSize`, by option and direction."},
    {"id": "debt.linter", "label": "Linter suppressions", "group": DEBT, "unit": "suppressions",
     "lower_is_better": True,
     "description": "`set_option linter.X false` and `@[nolint X]`, per linter."},
    {"id": "debt.linter_scope", "label": "Linter suppressions by scope", "group": DEBT,
     "unit": "suppressions", "lower_is_better": True,
     "description": "The same suppressions by form: `set_option ... in`, file- or section-wide, "
                    "or `@[nolint]`."},
    {"id": "debt.misc", "label": "erw, deprecations and adaptation notes", "group": DEBT,
     "unit": "occurrences", "lower_is_better": True,
     "description": "`erw` rewrites, `@[deprecated]` attributes and `#adaptation_note`s."},
    {"id": "kernel.slow", "label": "Slow declarations in the kernel", "group": KERNEL,
     "unit": "declarations", "lower_is_better": True,
     "description": "Declarations whose kernel type-checking takes at least 1 s, by duration "
                    "(scripts/tech_debt/kernel_times.py, measured daily on the changed modules)."},
    {"id": "kernel.time", "label": "Total kernel time", "group": KERNEL, "unit": "seconds",
     "lower_is_better": True,
     "description": "Sum of the kernel type-checking time over all measured modules."},
    {"id": "kernel.failed", "label": "Modules that failed the kernel measurement", "group": KERNEL,
     "unit": "modules", "lower_is_better": True,
     "description": "Modules for which kernel_times.py produced no result (timeout or error)."},
]

# metrics.py category (and item) -> kind.
UNFINISHED = {"sorry", "admit", "axiom declarations"}
CATEGORY_KIND = {
    metrics.LINTER: "debt.linter",
    metrics.LINTER_SCOPE: "debt.linter_scope",
    metrics.LIMITS: "debt.limits",
    metrics.BACKWARD: "debt.backward",
}


def kind_of(cat, item):
    if cat == metrics.OTHER:
        return "debt.unfinished" if item in UNFINISHED else "debt.misc"
    return CATEGORY_KIND.get(cat) or "debt." + re.sub(r"[^a-z0-9]+", "_", cat.lower()).strip("_")


def debt_metrics(per_file):
    out = {k["id"]: {} for k in KINDS if k["id"].startswith("debt.")}
    for (cat, item), n in metrics.totals(per_file).items():
        if n:
            out.setdefault(kind_of(cat, item), {})[item] = n
    return out


def kernel_record(table_path):
    """(metrics, kernel block) from a kernel_times.py table."""
    t = kernel_times.Table.load(table_path)
    thr = int(t.meta.get("threshold_ms", "1000"))
    # Disjoint buckets, so that the kind's total is the number of declarations above `thr`.
    bounds = sorted({thr, 10000, 60000})
    slow = {}
    for lo, hi in zip(bounds, bounds[1:] + [None]):
        name = f"{lo / 1000:g}–{hi / 1000:g} s" if hi else f"≥ {lo / 1000:g} s"
        slow[name] = sum(1 for v in t.decls.values() if v >= lo and (hi is None or v < hi))
    m = {
        "kernel.slow": slow,
        "kernel.time": {"total kernel time": round(sum(k for k, _, _ in t.modules.values()) / 1000)},
        "kernel.failed": {"failed modules": len(t.errors)},
    }
    top = sorted(t.decls.items(), key=lambda kv: (-kv[1], kv[0]))[:KERNEL_TOP]
    block = {"rev": t.meta.get("rev"), "threshold_ms": thr, "modules": len(t.modules),
             "top": [[ms, mod, name] for (mod, name), ms in top]}
    return m, block


# ---------------------------------------------------------------------------------------------
# Git

def git(*args):
    return metrics.git(*args).decode()


def commit_info(rev):
    sha, ct = git("show", "-s", "--format=%H %ct", rev).split()
    return sha, int(ct)


def iso(ts):
    return datetime.datetime.fromtimestamp(ts, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def day(ts):
    return iso(ts)[:10]


def daily_samples(ref, after_ts=None, since_day=None):
    """The last first-parent commit of `ref` on each UTC day, oldest first: [(sha, ct)]."""
    per_day = {}
    for line in git("log", "--first-parent", "--format=%H %ct", ref).splitlines():
        sha, ct = line.split()
        ct = int(ct)
        d = day(ct)
        if (after_ts is not None and ct <= after_ts) or (since_day and d < since_day):
            continue
        if d not in per_day or ct > per_day[d][1]:
            per_day[d] = (sha, ct)
    return [per_day[d] for d in sorted(per_day)]


class IncrementalCounter:
    """Counts commits one after the other, re-reading only the files that changed."""

    def __init__(self):
        self.rev = None
        self.per_file = None

    def count(self, rev):
        if self.rev is None:
            self.per_file = metrics.count_rev(rev)
        else:
            changed = [p for p in git("diff", "-z", "--name-only", "--no-renames", self.rev, rev)
                       .split("\0") if metrics.in_scope(p)]
            new = metrics.count_files(metrics.read_blobs(rev, changed))
            for p in changed:
                self.per_file.pop(p, None)
            self.per_file.update(new)
        self.rev = rev
        return debt_metrics(self.per_file)


# ---------------------------------------------------------------------------------------------
# The store

def load(data):
    path = os.path.join(data, "history.jsonl")
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def save(data, records, repo_url):
    os.makedirs(data, exist_ok=True)
    by_commit = {}
    for r in records:
        by_commit[r["commit"]] = r  # later records of a commit win
    records = sorted(by_commit.values(), key=lambda r: (r["date"], r["commit"]))
    tmp = os.path.join(data, "history.jsonl.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        for r in records:
            f.write(json.dumps(r, sort_keys=True, ensure_ascii=False, separators=(",", ":")) + "\n")
    os.replace(tmp, os.path.join(data, "history.jsonl"))
    meta_path = os.path.join(data, "meta.json")
    meta = {}
    if os.path.exists(meta_path):
        with open(meta_path, encoding="utf-8") as f:
            meta = json.load(f)
    # Kinds defined here come first, in this order; kinds only the existing meta.json knows
    # (added by hand, or by a later version) are kept after them.
    ours = {k["id"] for k in KINDS}
    meta.update({
        "schema": SCHEMA,
        "title": meta.get("title", "Weil conjectures: quality dashboard"),
        "repo_url": repo_url or meta.get("repo_url"),
        "updated": iso(time.time()),
        "kinds": KINDS + [k for k in meta.get("kinds", []) if k.get("id") not in ours],
    })
    with open(meta_path, "w", encoding="utf-8") as f:
        json.dump(meta, f, indent=1, ensure_ascii=False)
        f.write("\n")
    return records


def record(sha, ct, debt, source):
    return {"schema": SCHEMA, "commit": sha, "date": iso(ct), "source": source, "metrics": debt}


def run_samples(samples, counter, source, log=True):
    out = []
    for i, (sha, ct) in enumerate(samples):
        t0 = time.time()
        out.append(record(sha, ct, counter.count(sha), source))
        if log:
            print(f"[{i + 1}/{len(samples)}] {day(ct)} {sha[:10]}  {time.time() - t0:.1f} s",
                  file=sys.stderr)
    return out


# ---------------------------------------------------------------------------------------------
# Commands

def cmd_backfill(args):
    since = args.since
    if args.days is not None:
        since = day(time.time() - args.days * 86400)
    samples = daily_samples(args.ref, since_day=since)
    print(f"{len(samples)} commits to count ({samples[0][0][:10] if samples else '-'} .. "
          f"{samples[-1][0][:10] if samples else '-'})", file=sys.stderr)
    t0 = time.time()
    new = run_samples(samples, IncrementalCounter(), "backfill")
    old = {r["commit"]: r for r in load(args.data)}
    # Keep what a backfill does not know: kernel data and daily records.
    for r in new:
        prev = old.get(r["commit"])
        if prev:
            r["source"] = prev.get("source", r["source"])
            for k, v in prev.get("metrics", {}).items():
                if not k.startswith("debt."):
                    r["metrics"][k] = v
            if "kernel" in prev:
                r["kernel"] = prev["kernel"]
    records = save(args.data, list(old.values()) + new, args.repo_url)
    print(f"counted {len(new)} commits in {time.time() - t0:.0f} s; {len(records)} records",
          file=sys.stderr)


def cmd_update(args):
    sha, ct = commit_info(args.rev)
    records = load(args.data)
    counter = IncrementalCounter()
    new = []
    if records:
        last_ts = max(int(datetime.datetime.strptime(r["date"], "%Y-%m-%dT%H:%M:%SZ")
                          .replace(tzinfo=datetime.timezone.utc).timestamp()) for r in records)
        gap = [s for s in daily_samples(sha, after_ts=last_ts)
               if day(s[1]) != day(ct) and s[1] >= ct - args.max_gap_days * 86400]
        if gap:
            print(f"filling {len(gap)} missed days", file=sys.stderr)
            new += run_samples(gap, counter, "backfill")
    r = record(sha, ct, counter.count(sha), "daily")
    if args.kernel and os.path.exists(args.kernel):
        km, block = kernel_record(args.kernel)
        if block["rev"] and block["rev"] != sha:
            print(f"warning: the kernel table is for {block['rev'][:10]}, not {sha[:10]}; not recorded",
                  file=sys.stderr)
        else:
            r["metrics"].update(km)
            r["kernel"] = block
    new.append(r)
    save(args.data, records + new, args.repo_url)
    print(f"recorded {sha[:10]} ({day(ct)})" + (" with kernel timings" if "kernel" in r else ""),
          file=sys.stderr)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    b = sub.add_parser("backfill", help="record one commit per day from the history")
    b.add_argument("--data", required=True, help="the history directory")
    b.add_argument("--ref", default="origin/master")
    g = b.add_mutually_exclusive_group()
    g.add_argument("--since", help="first day, YYYY-MM-DD (default: the beginning)")
    g.add_argument("--days", type=int, help="the last N days")
    b.add_argument("--repo-url")
    u = sub.add_parser("update", help="record one commit")
    u.add_argument("--data", required=True)
    u.add_argument("--rev", required=True)
    u.add_argument("--kernel", help="kernel_times.py table measured at REV")
    u.add_argument("--repo-url")
    u.add_argument("--max-gap-days", type=int, default=400, help="fill at most this many missed days")
    args = p.parse_args()
    (cmd_backfill if args.cmd == "backfill" else cmd_update)(args)


if __name__ == "__main__":
    main()
