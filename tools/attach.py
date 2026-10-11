#!/usr/bin/env python3
"""Record that a node is already proved in the project's Lean (an attachment), without a reviewer.

Usage:
  tools/attach.py <group> <node> <declaration> [<declaration> ...] --note "<one line>" [--dry]

Who judges what: that the declarations state the node exactly is the judgement of two workers of the group (the one
who found them and an independent one who confirmed); this tool does the mechanical part. It refuses, saying why,
unless: the group holds the claim on the node; the node is unsplit or imported and has no Lean state yet; every
declaration is a declaration of the project in the current sorry map of slopmaster2 (a library declaration is not an
attachment: that node is a Mathlib leaf and is delivered as one); none contains `sorry` and no `sorry` is reachable
from them. Then it writes `lean` (note beginning "attached by the lead's tool", so that tools/lean_status.py keeps the
names) and `lean_audit.slopmaster2` (state closed), commits the node file on sheaf-dag under the merge lock with the
subject "Attach <node> (<group>): <declaration>", releases the claim and prints "ATTACHED <node> at <commit>".
--dry does the checks and writes nothing. Written by the launcher, 2026-10-10 (decision of the human: attachments
found by remote workers are confirmed on the remote side and recorded mechanically).
"""
from __future__ import annotations
import collections, fcntl, glob, gzip, json, pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
BRANCH = "slopmaster2"


def load():
    maps = sorted(glob.glob(str(ROOT / "local" / f"sorry_map_{BRANCH}_*.jsonl.gz")), key=lambda p: pathlib.Path(p).stat().st_mtime)
    maps = [m for m in maps if "_full" not in m] or maps
    if not maps: raise SystemExit("REFUSED: no sorry map of slopmaster2 in local/")
    with gzip.open(maps[-1], "rt") as fh: rows = [json.loads(l) for l in fh]
    owner = {r["n"]: r["o"] for r in rows}; own = {}; deps = collections.defaultdict(set)
    for r in rows:
        o = r["o"]; rec = own.setdefault(o, {"sorry": False, "kind": None, "module": None, "l1": 0, "l2": 0})
        rec["sorry"] |= bool(r["s"] or r["ts"])
        if r["n"] == o: rec.update(kind=r["k"], module=r["m"], l1=r["l1"], l2=r["l2"])
        for d in r["d"]:
            if owner.get(d, d) != o: deps[o].add(owner.get(d, d))
    return owner, own, deps, pathlib.Path(maps[-1]).name


def main() -> int:
    a = sys.argv[1:]; dry = "--dry" in a; note = ""
    if "--note" in a: i = a.index("--note"); note = a[i + 1] if i + 1 < len(a) else ""; del a[i:i + 2]
    a = [x for x in a if x != "--dry"]
    if len(a) < 3: print(__doc__); return 2
    g, nid, decls = a[0], a[1], list(dict.fromkeys(x.strip().strip(",`") for x in a[2:] if x.strip().strip(",`")))
    hits = list((ROOT / "dag" / "nodes").glob(f"*/{nid}.json"))
    if not hits: print(f"REFUSED: no node {nid}"); return 1
    owner, own, deps, mapname = load()
    lib = set()
    bad = []; recs = []
    for n in decls:
        o = owner.get(n, n)
        if o not in own:
            bad.append(f"{n}: not a declaration of the project on {BRANCH} ({mapname}); if it is a Mathlib declaration the node is a Mathlib leaf and is delivered as one, if the name is misspelt give the full name with namespaces"); continue
        if own[o]["sorry"]: bad.append(f"{n}: contains sorry"); continue
        seen = {o}; st = [o]; sor = []
        while st:
            x = st.pop()
            for y in deps.get(x, ()):
                if y in seen: continue
                seen.add(y)
                if y in own and own[y]["sorry"]: sor.append(y)
                else: st.append(y)
        if sor: bad.append(f"{n}: rests on sorry ({len(sor)} sorried declarations reachable, e.g. {', '.join(sorted(sor)[:4])})"); continue
        r = own[o]; recs.append({"name": o, "module": r["module"], "lines": [r["l1"], r["l2"]], "kind": r["kind"], "sorry": False})
    if bad: print("REFUSED:\n " + "\n ".join(bad)); return 1
    lockf = ROOT / "coord" / ".merge.lock"
    import mergelock
    with open(lockf, "a") as lf:
        try:
            mergelock.acquire(lf, lockf)
        except mergelock.LockTimeout as e:
            print(f"REFUSED: {e}"); return 1
        p = hits[0]; d = json.loads(p.read_text())
        cl = ROOT / "coord" / "claims" / f"{nid}.lock"
        who = json.loads(cl.read_text()).get("who") if cl.exists() else None
        if who != g: print(f"REFUSED: the claim on {nid} is held by {who}, not by {g}"); return 1
        if d.get("status") not in ("unsplit", "imported"): print(f"REFUSED: {nid} has status {d.get('status')}"); return 1
        cur = ((d.get("lean_audit") or {}).get(BRANCH) or {})
        if cur.get("state") not in (None, "none"): print(f"REFUSED: {nid} already has the Lean state {cur.get('state')} on {BRANCH} ({[x.get('name') for x in cur.get('decls') or []][:4]}); this is the maintainer's to sort out"); return 1
        if dry: print(f"WOULD ATTACH {nid}: " + ", ".join(f"{r['name']} ({r['module']}:{r['lines'][0]})" for r in recs)); return 0
        day = time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())
        d["lean"] = {"branch": BRANCH, "declarations": [r["name"] for r in recs],
                     "note": f"attached by the lead's tool attach.py {day} for group {g}, the statement match confirmed by two remote workers, sorry-free and resting on no sorry by {mapname}: {note}"[:1500]}
        la = dict(d.get("lean_audit") or {}); la[BRANCH] = {"state": "closed", "decls": recs, "missing": [], "open": []}; d["lean_audit"] = la
        p.write_text(json.dumps(d, indent=1, ensure_ascii=False) + "\n")
        rel = str(p.relative_to(ROOT))
        def git(*x): return subprocess.run(["git", "-C", str(ROOT), *x], capture_output=True, text=True)
        r = git("commit", "-q", "-m", f"Attach {nid} ({g}): {recs[0]['name']}", "--", rel)
        if r.returncode:
            time.sleep(2); r = git("commit", "-q", "-m", f"Attach {nid} ({g}): {recs[0]['name']}", "--", rel)
        if r.returncode:
            git("checkout", "--", rel); print("REFUSED: the commit failed: " + (r.stderr or r.stdout).strip()[:300]); return 1
        h = git("rev-parse", "--short", "HEAD").stdout.strip()
    subprocess.run([sys.executable, str(ROOT / "tools" / "claim.py"), "release", g, nid, f"attached by tools/attach.py at {h}: {recs[0]['name']}"], capture_output=True, text=True)
    print(f"ATTACHED {nid} at {h}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
