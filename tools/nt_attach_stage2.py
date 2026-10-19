"""Lead-only registration of checked existing stage-2 statements, including open proofs.

Called by attach.py --stage2. The explicit compiler-produced map describes the side
overlay; its sorry states are preserved, so registration never closes an open proof.
"""
import argparse
import collections
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main(root):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("group", choices=["L"])
    parser.add_argument("node")
    parser.add_argument("declarations", nargs="+")
    parser.add_argument("--stage2", action="store_true", required=True)
    parser.add_argument("--map", required=True)
    parser.add_argument("--note", required=True)
    parser.add_argument("--dry", action="store_true")
    args = parser.parse_args()
    if os.environ.get("SHEAF_LEAD") != "L-only":
        raise SystemExit("REFUSED: stage-2 attachment requires SHEAF_LEAD=L-only")
    from mergelock import merge_lock
    map_path = Path(args.map).resolve()
    opener = gzip.open if map_path.suffix == ".gz" else open
    with opener(map_path, "rt") as handle:
        rows = [json.loads(line) for line in handle]
    owner = {r["n"]: r["o"] for r in rows}
    own, deps = {}, collections.defaultdict(set)
    for row in rows:
        name = row["o"]
        rec = own.setdefault(name, {"sorry": False})
        rec["sorry"] |= bool(row["s"] or row["ts"])
        if row["n"] == name:
            rec.update(module=row["m"], kind=row["k"], lines=[row["l1"], row["l2"]])
        deps[name].update(owner.get(d, d) for d in row["d"] if owner.get(d, d) != name)
    decls = list(dict.fromkeys(args.declarations))
    records = []
    for name in decls:
        if owner.get(name, name) != name or name not in own or "module" not in own[name]:
            raise SystemExit("REFUSED: not a primary project declaration in the supplied map: " + name)
        rec = own[name]
        if not (root / "lean" / (rec["module"].replace(".", "/") + ".lean")).is_file():
            raise SystemExit("REFUSED: declaration source is absent from the side library: " + name)
        records.append(dict(name=name, **rec))
    seen, todo, frontier = set(decls), [n for n in decls if not own[n]["sorry"]], set()
    while todo:
        for name in deps.get(todo.pop(), ()):
            if name in seen or name not in own:
                continue
            seen.add(name)
            if own[name]["sorry"]:
                frontier.add(name)
            else:
                todo.append(name)
    state = ("sorry_here" if any(r["sorry"] for r in records)
             else "rests_on_sorry" if frontier else "closed")
    audit = {"state": state, "decls": records, "missing": [], "open": [
        dict(name=n, module=own[n]["module"], lines=own[n]["lines"], kind=own[n]["kind"])
        for n in sorted(frontier)]}
    hits = list((root / "dag/nodes").glob("*/" + args.node + ".json"))
    if len(hits) != 1:
        raise SystemExit("REFUSED: expected exactly one node: " + args.node)
    path = hits[0]
    claim_path = root / "coord/claims" / (args.node + ".lock")
    with merge_lock(root / "coord/.merge.lock"):
        node = json.loads(path.read_text())
        if node.get("status") != "split" or not node.get("reviewed"):
            raise SystemExit("REFUSED: stage-2 attachment requires a reviewed split")
        if node.get("lean") or ((node.get("lean_audit") or {}).get("slopmaster2") or {}).get("state") not in (None, "none"):
            raise SystemExit("REFUSED: node already has a Lean record")
        claim = json.loads(claim_path.read_text()) if claim_path.exists() else None
        if claim and claim.get("who") != args.group:
            raise SystemExit("REFUSED: node claimed by " + str(claim.get("who")))
        print(f"{args.node}: {state}; {len(records)} declaration(s); {len(frontier)} open dependency owners")
        if args.dry:
            print("WOULD ATTACH " + args.node)
            return 0
        claim_path.parent.mkdir(exist_ok=True)
        if not claim:
            with claim_path.open("x") as handle:
                json.dump({"who": args.group, "t": time.time(),
                           "since": time.strftime("%FT%TZ", time.gmtime()), "stage": 2}, handle)
        node["lean"] = {"branch": "slopmaster2", "existing": True,
                        "module": records[0]["module"], "declaration": decls[0], "declarations": decls,
                        "note": "attached by the lead's tool attach.py --stage2; source and statement checked by L; "
                        + state + " by " + map_path.name + ": " + args.note}
        node.setdefault("lean_audit", {})["slopmaster2"] = audit
        original = path.read_text()
        path.write_text(json.dumps(node, indent=1, ensure_ascii=False) + "\n")
        rel = str(path.relative_to(root))
        msg = (f"Attach stage-2 statement {args.node}: {decls[0]}\n\n"
               "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>")
        print("COMMIT FILE " + rel, flush=True)
        sys.path.insert(0, str(root / "tools"))
        import livedag
        if livedag.active():    # one DAG (2026-10-18): dag/nodes is the live DAG; commit the node there
            try:
                head = livedag.commit_live([rel], msg) or "unchanged"
                result = subprocess.CompletedProcess([], 0)
            except Exception as exc:  # noqa: BLE001
                print("live commit failed: " + str(exc)[:300], flush=True)
                result = subprocess.CompletedProcess([], 1)
        else:
            result = subprocess.run(["git", "-c", "user.name=Bin Wu", "-c",
                                     "user.email=844524296@qq.com", "commit", "-q", "-m", msg, "--", rel], cwd=root)
        if result.returncode:
            path.write_text(original)
            if not claim:
                claim_path.unlink(missing_ok=True)
            raise SystemExit(result.returncode)
        if not livedag.active():
            head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    subprocess.run([sys.executable, str(root / "tools/claim.py"), "release", args.group, args.node,
                    "stage-2 attachment at " + head], check=True, cwd=root)
    print("ATTACHED " + args.node + " at " + head, flush=True)
    return 0   # 2026-10-19: one repository; nothing to promote
