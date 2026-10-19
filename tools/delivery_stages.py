#!/usr/bin/env python3
"""Delivery branches with their stage (launcher, 2026-10-16): `branch<TAB>sha<TAB>unix time<TAB>stage` for every
refs/heads/deliver/<group>/<item>. The stage is the item's stage in coord/queue.tsv; for an item the queue no longer
lists, 2 when the branch changes a file under lean/, else 1. The stage-1 and stage-2 review loops each take only their
own stage (they reviewed each other's deliveries before)."""
import pathlib, subprocess
R = pathlib.Path(__file__).resolve().parent.parent
main = subprocess.run(["git", "branch", "--show-current"], cwd=R, capture_output=True, text=True).stdout.strip() or "sheaf-dag"
q = {}
for l in (R / "coord/queue.tsv").read_text().splitlines():
    r = l.split("\t")
    if len(r) > 1 and not l.startswith("#"): q[r[0]] = r[1]
out = subprocess.run(["git", "for-each-ref", "--format=%(refname:short)\t%(objectname)\t%(committerdate:unix)", "refs/heads/deliver/"],
                     cwd=R, capture_output=True, text=True).stdout
for line in out.splitlines():
    p = line.split("\t")
    if len(p) != 3 or p[0].count("/") < 2: continue
    item = p[0].split("/", 2)[2]
    st = q.get(item)
    if "." in item:          # retirement of ~/weil-newtargets (2026-10-19): a module item is stage 3 (one repository)
        st = "3"
    elif st not in ("1", "2"):
        d = subprocess.run(["git", "diff", "--name-only", f"{main}...{p[1]}", "--", "lean"], cwd=R, capture_output=True, text=True).stdout
        st = "2" if d.strip() else "1"
    print("\t".join(p + [st]))
