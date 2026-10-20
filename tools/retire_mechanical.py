#!/usr/bin/env python3
"""Mechanical retirement of Sheaf copies whose upstream twin has the same statements (the human, 2026-10-20: once
upstream has merged code, our library uses upstream's version wherever possible, above all when it is identical).

The copies of coord/retire-items.tsv of class IDENTICAL, PROOFDIFF or REEXPORT (same statements: identical, proofs
differ, or a re-export of the twin) whose twin exists in lean/: every import of the copy in lean/ (our modules, the
root files, and upstream files that import it privately) is switched to the twin (a line becomes redundant when the
file imports the twin already, and is dropped), the DAG nodes whose `lean.module` is the copy point at the twin, and
the copy is deleted. No worker and no queue item; what then fails to compile goes through the sync's quarantine.
Copies of the other classes (DIFFERENT, SUPERSET, PROOFDIFF_UNSAFE) stay `retire` items for workers.

Used by ~/cc1/upsync-quick.py in every sync, after the merge (and by hand: --dry-run prints the plan).
  tools/retire_mechanical.py [--dry-run] [--json OUT]
"""
from __future__ import annotations
import json, pathlib, re, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
ITEMS = ROOT / "coord" / "retire-items.tsv"
MECHANICAL = ("IDENTICAL", "PROOFDIFF", "REEXPORT")
IMPORT = re.compile(r"^((?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?)([\w.']+)(\s*(?:--.*)?)$")


def plan() -> dict[str, str]:
    """copy -> twin, for the mechanical classes, both files present"""
    out = {}
    try:
        lines = ITEMS.read_text().splitlines()
    except OSError:
        return out
    for l in lines:
        r = l.split("\t")
        if l.startswith("#") or len(r) < 5 or r[4] not in MECHANICAL:
            continue
        copy, twin = r[2], r[3]
        if li.file_of(copy).is_file() and li.file_of(twin).is_file():
            out[copy] = twin
    return out


def rewrite(text: str, own: str, mapping: dict[str, str]) -> str:
    lines = text.split("\n")
    have = set(li.imports_of(text))
    out, changed = [], False
    for line in lines:
        m = IMPORT.match(line)
        if m and m.group(2) in mapping:
            new = mapping[m.group(2)]
            changed = True
            if new == own or new in have:
                continue                      # the twin is imported already (or is the file itself)
            have.add(new)
            line = m.group(1) + new + m.group(3)
        out.append(line)
    return "\n".join(out) if changed else text


def apply(mapping: dict[str, str], write: bool = True) -> dict:
    """returns {"lean": {path under lean/: previous bytes or None}, "nodes": [paths], "deleted": [modules]}"""
    prev: dict[str, bytes | None] = {}
    files = list(li.LEAN.glob("*.lean"))
    for d in ("Sheaf", "WeilConjectures"):
        files += list((li.LEAN / d).rglob("*.lean"))
    for f in files:
        rel = str(f.relative_to(li.LEAN))
        if "/." in "/" + rel:
            continue
        mod = rel[:-5].replace("/", ".")
        if mod in mapping:
            continue
        try:
            text = f.read_text()
        except OSError:
            continue
        if "Sheaf." not in text:
            continue
        new = rewrite(text, mod, mapping)
        if new != text:
            prev[rel] = text.encode()
            if write:
                f.write_text(new)
    nodes = []
    for p in sorted((ROOT / "dag" / "nodes").glob("*/*.json")):
        t = p.read_text()
        if '"Sheaf.' not in t:
            continue
        try:
            n = json.loads(t)
        except ValueError:
            continue
        l = n.get("lean")
        if isinstance(l, dict) and l.get("module") in mapping:
            tw = mapping[l["module"]]
            l["module"] = tw
            if "file" in l:
                l["file"] = "lean/" + tw.replace(".", "/") + ".lean"
            nodes.append(str(p.relative_to(ROOT)))
            if write:
                p.write_text(json.dumps(n, ensure_ascii=False, indent=1) + "\n")
    for copy in mapping:
        f = li.file_of(copy)
        rel = str(f.relative_to(li.LEAN))
        prev[rel] = f.read_bytes()
        if write:
            f.unlink()
    return {"lean": prev, "nodes": nodes, "deleted": sorted(mapping)}


def main() -> int:
    a = sys.argv[1:]
    m = plan()
    res = apply(m, write="--dry-run" not in a)
    summary = {"copies": len(m), "lean_files": len(res["lean"]), "nodes": len(res["nodes"])}
    if "--json" in a:
        pathlib.Path(a[a.index("--json") + 1]).write_text(json.dumps({**summary, "deleted": res["deleted"],
                                                                      "nodes": res["nodes"]}, indent=1))
    print(f"mechanical retirement: {summary['copies']} Sheaf copies -> their twins; {summary['lean_files']} Lean files "
          f"(consumers rewritten + copies deleted), {summary['nodes']} DAG nodes re-pointed"
          + (" (dry run)" if "--dry-run" in a else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
