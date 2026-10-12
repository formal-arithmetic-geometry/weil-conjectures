#!/usr/bin/env python3
"""Which review a stage-2 delivery gets (decision of the human, 2026-10-11: tiered review).

Usage:  tools/review_class.py <group> <item>      prints "AUTO" or "FULL: <reason>"
        tools/review_class.py list                every delivery branch with its class

Stage 3 (decision of the human, 2026-10-12: no Claude reviewer in stage 3). An item that is a module of the library
(Sheaf.<...> or WeilConjectures.<...>) is classified by tools/stage3_delivery.py and gets one of two classes:
  AUTO   the delivery changes only proofs of the item's module: one module, no node file, no change record, nothing
         other modules see changed (leanindex.interface_changes), no declaration added (public), removed or restated,
         no public import changed in a module with importers, no removed import of a unit-route module, no `sorry`
         left in a declaration it adds or rewrites, no axiom/unsafe/extern/opaque, no STATEMENT-DISPUTED, not the
         repair of a return, no failed automatic landing of this head. Landed by ~/cc1/autoland3.py in a
         batch (tools/batch_land.py): the static checks, no compile on the server, and the global build verifies the
         whole batch; with reviewer AUTO the landing must be a proof landing.
  CODEX  everything else, with the reasons (a statement, a definition, an import other modules see, nodes, a change
         record, several modules, a failed static check, ...): read by the independent Codex reviewer on the other
         machine, whose verdict a script executes with tools/merge_delivery.py <G> <module> --stage 3 --reviewer <ID>
         --head <sha> or tools/merge_delivery.py return <G> <module> <reasons> (both with SHEAF_LEAD=L-only).
`FULL` is not used for a stage-3 delivery. Stage 2, below, is unchanged.

FULL (read by a reviewer sub-agent of the lead before it lands), when any of these holds:
  the item is a definition; the delivery adds a node (a new definition node) or changes another existing node (a
  dependency module); the item's statement is corrected (statement differs from sheaf-dag, or statement_change added);
  [CODEX: an independent Codex reviewer on the other machine, xreview.py, since 2026-10-12: `existing: true` records and repairs of returns]
  the record says `existing: true` (the node is mapped to a declaration nobody compiled against it); the report says
  STATEMENT-DISPUTED; the item was returned before (a repair); more than one module; the automatic landing of this
  head failed (local/autoland-failed.tsv); or the item falls in the sample (one statement in four, by a hash of its id).
AUTO (landed by ~/cc1/autoland.py with tools/merge_delivery.py --stage 2 --reviewer AUTO after the second Codex reading
  and the tool's mechanical checks and compile; `reviewed_lean.reviewer` = "AUTO" marks it for a later audit):
  every other delivery, i.e. the plain statement of a lemma with `sorry`.
"""
from __future__ import annotations
import os, hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
if not (ROOT / "dag").exists(): ROOT = pathlib.Path.home() / "weil-conjectures-sheaf"
SAMPLE = 10
def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout
def show(ref, path):
    r = subprocess.run(["git", "-C", str(ROOT), "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
def classify(g: str, item: str, D=None):
    br = f"deliver/{g}/{item}"; head = git("rev-parse", br).strip()
    if not head: return "NONE", "no such branch", ""
    if "." in item:   # a stage-3 item is a module; a stage-1/2 item is a node id (no dot)
        f3 = ROOT / "local" / "autoland-failed.tsv"
        if f3.exists():
            for l in f3.read_text().split("\n"):
                p = l.split("\t")
                if len(p) >= 3 and p[0] == g and p[1] == item and head.startswith(p[2]) and "merge.lock held" not in l:
                    return "CODEX", "automatic landing failed: " + (p[3] if len(p) > 3 else ""), head
        sys.path.insert(0, str(ROOT / "tools")); import stage2_delivery as s2, stage3_delivery as s3
        try:
            if D is None:   # tools/batch_land.py passes its own reading, so that a delivery is read once
                D = s3.read_delivery(s2.Git(ROOT), br, "sheaf-dag", g, item)
            why = s3.classify(D, g, item)
        except Exception as e:   # a delivery the tool cannot read needs a reader
            return "CODEX", "the delivery could not be read: " + repr(e)[:200], head
        # the human, 2026-10-12: in stage 3 a proof that compiles is checked by the compiler, not by a reader. A reader
        # is kept only where the compiler cannot see the harm: an existing statement or interface changed, a declaration
        # removed, a unit-route import removed, a disputed statement, a forbidden keyword, failed static checks.
        KEEP = ("reader required:", "the static checks fail", "statement changed", "removes declarations", "removes the import of unit-route",
                "new ", "STATEMENT-DISPUTED", "changes what other modules see")
        allwhy = why
        why = [w for w in why if w.startswith(KEEP) and not w.endswith(": (new module)")]
        # "compiler-only": landed without a reader although it is more than a proof of one module (new lemmas, nodes,
        # modules); the lander passes --reviewer COMPILER so that the proofs-only guard of AUTO does not revert it
        return ("AUTO", ("compiler-only: " + "; ".join(allwhy)) if allwhy else "", head) if not why else ("CODEX", "; ".join(why), head)
    base = git("merge-base", "sheaf-dag", br).strip()
    ch = [l.split("\t") for l in git("diff", "--name-status", f"{base}..{br}").strip().split("\n") if l]
    nodes = [(c[0], c[-1]) for c in ch if c[-1].startswith("dag/nodes/") and c[-1].endswith(".json")]
    mods = [c[-1] for c in ch if c[-1].startswith("lean/") and c[-1].endswith(".lean")]
    mine = [p for s, p in nodes if pathlib.Path(p).stem == item]
    if len(mine) != 1: return "FULL", "the item's node file is not (exactly once) in the delivery", head
    try: d = json.loads(show(br, mine[0]) or ""); b = json.loads(show(base, mine[0]) or "{}")
    except Exception: return "FULL", "a node file is not valid JSON", head
    f = ROOT / "local" / "autoland-failed.tsv"
    if f.exists():
        for l in f.read_text().split("\n"):
            p = l.split("\t")
            if len(p) >= 3 and p[0] == g and p[1] == item and head.startswith(p[2]): return "FULL", "automatic landing failed: " + (p[3] if len(p) > 3 else ""), head
    ret = ROOT / "coord" / "returns" / f"{g}.md"
    if ret.exists() and f"## {item} (" in ret.read_text(): return "CODEX", "repair of a returned delivery (the return said exactly what to change)", head
    if d.get("kind") != "statement": return "FULL", f"the item is a {d.get('kind')}", head
    if any(s == "A" for s, p in nodes): return "FULL", "new definition node(s)", head
    if len(nodes) > 1: return "FULL", "another existing node is changed (dependency module)", head
    if len(mods) > 1: return "FULL", "several modules", head
    if d.get("statement") != b.get("statement") or d.get("statement_change") != b.get("statement_change"): return "FULL", "statement corrected", head
    if d.get("stmt_deps") != b.get("stmt_deps") or d.get("proof") != b.get("proof"): return "FULL", "stmt_deps or proof changed", head
    lean = d.get("lean") or {}
    if lean.get("existing") or not mods: return "CODEX", "existing: true record (no module)", head
    rep = show(br, f"coord/reports/{g}/{item}.md") or ""
    import re
    if any(not re.match(r"\s*`?\s*(none|no\b|n/a|not applicable|nothing)", m, re.I) for m in re.findall(r"STATEMENT-DISPUTED:(.{0,40})", rep)):
        return "FULL", "STATEMENT-DISPUTED", head
    if int(hashlib.sha1(item.encode()).hexdigest(), 16) % SAMPLE == 0: return "FULL", f"sample (1 in {SAMPLE})", head
    return "AUTO", "", head
def branches():
    out = []
    for l in git("for-each-ref", "--format=%(refname:short)", "refs/heads/deliver").split("\n"):
        p = l.split("/")
        if len(p) == 3: out.append((p[1], p[2]))
    return out
if __name__ == "__main__":
    a = sys.argv[1:]
    if a == ["list"]:
        # With some 150 branches a full classification takes minutes, and the reader's script lists every 30 s:
        # a class is kept per branch head for 20 minutes (local/review-class-cache.json; a new head is classified at once).
        import json as _j, time as _t
        cf = ROOT / "local" / "review-class-cache.json"
        try: cache = _j.loads(cf.read_text())
        except (OSError, ValueError): cache = {}
        now = _t.time(); new = {}
        for g, i in branches():
            hd = git("rev-parse", f"deliver/{g}/{i}").strip(); k = f"{g}/{i}"
            e = cache.get(k)
            if e and e[0] == hd and now - e[3] < 1200: c, why, h = e[1], e[2], hd
            else:
                c, why, h = classify(g, i); e = [h, c, why, now]
            new[k] = [hd, c, why, e[3]]
            print(f"{c}\t{g}\t{i}\t{h[:9]}\t{why}", flush=True)
        try:
            tmp = cf.with_suffix(".tmp%d" % os.getpid()); tmp.write_text(_j.dumps(new)); tmp.replace(cf)
        except OSError: pass
    elif len(a) == 2:
        c, why, h = classify(*a); print(c if c == "AUTO" else f"{c}: {why}")
    else: print(__doc__); sys.exit(2)
