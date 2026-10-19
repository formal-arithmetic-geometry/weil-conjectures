"""Axiom check of the DAG nodes whose live module has no sorry of its own but imports one (the human, 2026-10-16: stage 2
is pruned below what stage 3 finished). Writes local/stage2/live-axioms.json: declaration -> true when its axioms do not
include sorryAx. Run by hand or periodically: python3 tools/live_axioms.py. One Lean file against the live project's
published build (tools/lean_file.sh there); tools/live_closed.py reads the result."""
import json, os, pathlib, re, subprocess, sys, time
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import live_closed as lc, dag_queue as dq

OUT = lc.ROOT / "local" / "stage2" / "live-axioms.json"


def decls(rec):
    out = [rec["declaration"]] if rec.get("declaration") else []
    return out + [x for x in rec.get("declarations") or [] if isinstance(x, str) and x not in out]


def main():
    closed = lc.closed(); src = lc.LIVE / "lean"
    want, mods = [], set()
    for i, d in dq.load().items():
        rec = d.get("lean")
        if not isinstance(rec, dict) or not rec.get("module") or rec["module"] in closed: continue
        p = src / (rec["module"].replace(".", "/") + ".lean")
        if not p.is_file(): continue
        # 2026-10-18 (L, propagation): a module with sorries of its own is asked too; only the node's named declarations
        # are checked, so a proved declaration next to an open one closes its node (lem-sfb-dc-upper-star-preserves).
        if not (src / ".lake/build/lib/lean" / (rec["module"].replace(".", "/") + ".olean")).is_file(): continue   # not built: no target uses it
        ds = decls(rec)
        if ds: want += ds; mods.add(rec["module"])
    if not want: OUT.write_text(json.dumps({"checked": time.time(), "ok": {}})); return
    by_mod = {}
    for i, d in dq.load().items():
        rec = d.get("lean")
        if isinstance(rec, dict) and rec.get("module") in mods: by_mod.setdefault(rec["module"], []).extend(decls(rec))
    sb = src / ".sandbox" / "_sheaf"; sb.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, SHEAF_FILE_TIMEOUT="900")
    ok, failed = {}, []

    def run(chunk, tag):
        # Modules that declare the same name cannot be imported together: a failing chunk is split in two.
        f = sb / f"Axioms_Stage2Prune_{tag}.lean"
        names = [x for m in chunk for x in dict.fromkeys(by_mod[m])]
        f.write_text("".join(f"import {m}\n" for m in chunk) + "".join(f"#print axioms {x}\n" for x in names))
        r = subprocess.run(["tools/lean_file.sh", str(f.relative_to(lc.LIVE))], cwd=lc.LIVE, env=env, capture_output=True, text=True, timeout=1200)
        text = r.stdout + r.stderr
        got = {m.group(1): "sorryAx" not in (m.group(3) or "")
               for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)}
        f.unlink(missing_ok=True)
        if got or len(chunk) == 1:
            ok.update(got)
            if not got: failed.append(chunk[0])
            return
        h = len(chunk) // 2
        run(chunk[:h], tag + "a"); run(chunk[h:], tag + "b")

    mods = sorted(mods)
    for k in range(0, len(mods), 40):
        run(mods[k:k + 40], str(k))
    OUT.write_text(json.dumps({"checked": time.time(), "ok": ok, "asked": len(want), "unchecked_modules": failed}))
    print(f"{len(ok)} of {len(want)} declarations checked, {sum(ok.values())} without sorryAx; {len(failed)} modules could not be checked")


if __name__ == "__main__":
    main()
