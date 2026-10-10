#!/usr/bin/env python3
"""Per-group numbers for groups on other machines (roles/maintainer.md §7).

  tools/group_stats.py            print the table for coord/STATE.md
  tools/group_stats.py --json     the same as JSON

Merged: lines "<group> done <item> ... merged by L" of coord/deliveries.log (written by merge_delivery.py).
Returned: lines "delivery of <group>: <item> returned" or "returned deliver/<group>/<item> (" of coord/ledger.md (one per return; an item returned
twice counts twice). Claims: coord/claims/*.lock whose "who" is the group, with their age in hours.
A group is any claim holder or delivery group other than L.
"""
import datetime, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
groups = {}

def g(name):
    return groups.setdefault(name, {"merged": [], "returned": [], "abandoned": [], "claims": []})

p = ROOT / "coord" / "deliveries.log"
if p.exists():
    for line in p.read_text().splitlines():
        m = re.match(r"\S+ (\S+) abandoned (\S+):", line)
        if m:
            g(m.group(1))["abandoned"].append(m.group(2))
        m = re.match(r"\S+ (\S+) done (\S+) .*merged by L", line)
        if m and m.group(1) != "L":
            g(m.group(1))["merged"].append(m.group(2))
p = ROOT / "coord" / "ledger.md"
if p.exists():
    lines = p.read_text().splitlines()
    for n, line in enumerate(lines):
        m = re.search(r"delivery of (\S+): (\S+) returned", line)
        if m:
            g(m.group(1))["returned"].append(m.group(2))
        # the line merge_delivery.py return writes since 2026-10-10 evening; the lead wrote the same form by hand next to
        # the older tool's line, so it is counted only when no such line for the item stands in the 10 lines before
        for m in re.finditer(r"returned deliver/(\S+?)/(\S+) \(", line):
            if not any(f"delivery of {m.group(1)}: {m.group(2)} returned" in x for x in lines[max(0, n - 10):n + 1]):
                g(m.group(1))["returned"].append(m.group(2))
now = datetime.datetime.now(datetime.UTC)
for lock in sorted((ROOT / "coord" / "claims").glob("*.lock")):
    try:
        d = json.loads(lock.read_text())
    except Exception:
        continue
    who = d.get("who")
    if who and who != "L":
        age = (now - datetime.datetime.fromtimestamp(d["t"], datetime.UTC)).total_seconds() / 3600
        g(who)["claims"].append((lock.stem, round(age, 1)))

if "--json" in sys.argv:
    print(json.dumps(groups, indent=1))
else:
    print("| group | merged | returned | abandoned | claims held (age, h) |")
    print("|---|---|---|---|---|")
    for name in sorted(groups):
        d = groups[name]
        claims = ", ".join(f"{c} ({a})" for c, a in d["claims"]) or "none"
        print(f"| {name} | {len(d['merged'])} | {len(d['returned'])} | {len(d['abandoned'])} | {len(d['claims'])}: {claims} |")
