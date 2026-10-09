#!/usr/bin/env python3
"""Per-group numbers for groups on other machines (roles/maintainer.md §7).

  tools/group_stats.py            print the table for coord/STATE.md
  tools/group_stats.py --json     the same as JSON

Merged: lines "<group> done <item> ... merged by L" of coord/deliveries.log (written by merge_delivery.py).
Returned: lines "delivery of <group>: <item> returned" of coord/ledger.md (one per return; an item returned
twice counts twice). Claims: coord/claims/*.lock whose "who" is the group, with their age in hours.
A group is any claim holder or delivery group other than L.
"""
import datetime, json, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
groups = {}

def g(name):
    return groups.setdefault(name, {"merged": [], "returned": [], "claims": []})

p = ROOT / "coord" / "deliveries.log"
if p.exists():
    for line in p.read_text().splitlines():
        m = re.match(r"\S+ (\S+) done (\S+) .*merged by L", line)
        if m and m.group(1) != "L":
            g(m.group(1))["merged"].append(m.group(2))
p = ROOT / "coord" / "ledger.md"
if p.exists():
    for line in p.read_text().splitlines():
        m = re.search(r"delivery of (\S+): (\S+) returned", line)
        if m:
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
    print("| group | merged | returned | claims held (age, h) |")
    print("|---|---|---|---|")
    for name in sorted(groups):
        d = groups[name]
        claims = ", ".join(f"{c} ({a})" for c, a in d["claims"]) or "none"
        print(f"| {name} | {len(d['merged'])} | {len(d['returned'])} | {len(d['claims'])}: {claims} |")
