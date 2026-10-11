#!/usr/bin/env python3
"""Which review a stage-2 delivery gets (decision of the human, 2026-10-11: tiered review).

Usage:  tools/review_class.py <group> <item>      prints "AUTO" or "FULL: <reason>"
        tools/review_class.py list                every delivery branch with its class

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
import hashlib, json, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
if not (ROOT / "dag").exists(): ROOT = pathlib.Path.home() / "weil-conjectures-sheaf"
SAMPLE = 10
def git(*a):
    return subprocess.run(["git", "-C", str(ROOT), *a], capture_output=True, text=True).stdout
def show(ref, path):
    r = subprocess.run(["git", "-C", str(ROOT), "show", f"{ref}:{path}"], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
def classify(g: str, item: str):
    br = f"deliver/{g}/{item}"; head = git("rev-parse", br).strip()
    if not head: return "NONE", "no such branch", ""
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
        for g, i in branches():
            c, why, h = classify(g, i); print(f"{c}\t{g}\t{i}\t{h[:9]}\t{why}")
    elif len(a) == 2:
        c, why, h = classify(*a); print(c if c == "AUTO" else f"{c}: {why}")
    else: print(__doc__); sys.exit(2)
