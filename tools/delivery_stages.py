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
rows = [l.split("\t") for l in out.splitlines()]
rows = [p for p in rows if len(p) == 3 and p[0].count("/") >= 2]
# 2026-10-19 (hot path: one `git diff main...sha` per unlisted branch took ~100 s for 110 node branches in live): a
# delivery is one commit on its base, so its own commit's files decide; one `git diff-tree --stdin` for all of them
need = [p[1] for p in rows if "." not in p[0].split("/", 2)[2] and q.get(p[0].split("/", 2)[2]) not in ("1", "2")]
lean_heads = set()
if need:
    dt = subprocess.run(["git", "diff-tree", "--stdin", "-r", "--name-only", "--", "lean"], cwd=R, input="\n".join(need) + "\n",
                        capture_output=True, text=True).stdout
    cur = None
    for l in dt.splitlines():
        if len(l) == 40 and all(c in "0123456789abcdef" for c in l): cur = l
        elif l.strip() and cur: lean_heads.add(cur)
for p in rows:
    item = p[0].split("/", 2)[2]
    st = q.get(item)
    if "." in item:          # retirement of ~/weil-newtargets (2026-10-19): a module item is stage 3 (one repository)
        st = "3"
    elif st not in ("1", "2"):
        st = "2" if p[1] in lean_heads else "1"
    print("\t".join(p + [st]))
