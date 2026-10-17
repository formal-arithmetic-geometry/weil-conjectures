#!/usr/bin/env python3
"""Assumed results (the human, 2026-10-17): coord/assumed.tsv of the live project lists the DAG nodes a batch ASSUMES
instead of proving, with their Lean declarations. For the batches that assume it, such a node counts as finished in
stages 1 and 2 (tools/dag_queue.py: never an item, nothing waits for it, its stmt_deps are not reached through it), and
its Lean declarations are axioms of the stage-3 sorry route (tools/sorry_route.py: not descended into, their `sorry`s are
not that batch's work). For every other batch nothing changes (batch 4 proves Poincare duality, so its route keeps the
sorries of Poincare.lean).

Format (tab-separated, `#` comments): node id, Lean declarations (comma-separated, fully qualified), batches (comma-
separated numbers), reason. The file is read from this project's coord/ and otherwise from the live project's, so the
new-targets project (which reads the live DAG) and the live project share one list.
Usage: tools/assumed.py      print the list as read"""
import pathlib, re

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIVE = pathlib.Path("/home/ubuntu/weil-conjectures-sheaf")
_CACHE: dict = {}


def path() -> pathlib.Path | None:
    for p in (ROOT / "coord" / "assumed.tsv", LIVE / "coord" / "assumed.tsv"):
        if p.is_file():
            return p
    return None


def _bn(b) -> str:
    """'5', 5, 'batch5' -> 'batch5'"""
    m = re.fullmatch(r"(?:batch)?(\d+)", str(b).strip())
    return f"batch{m.group(1)}" if m else str(b).strip()


def rows() -> list[dict]:
    p = path()
    if p is None:
        return []
    st = p.stat(); key = (str(p), st.st_mtime_ns, st.st_size)
    if _CACHE.get("key") != key:
        out = []
        for line in p.read_text().splitlines():
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            c = line.split("\t")
            if len(c) < 3:
                continue
            out.append({"node": c[0].strip(),
                        "decls": [x.strip() for x in c[1].split(",") if x.strip()],
                        "batches": {_bn(x) for x in c[2].split(",") if x.strip()},
                        "reason": c[3].strip() if len(c) > 3 else ""})
        _CACHE.update(key=key, rows=out)
    return _CACHE["rows"]


def nodes() -> dict[str, set[str]]:
    """node id -> the batches that assume it"""
    out: dict[str, set[str]] = {}
    for r in rows():
        out.setdefault(r["node"], set()).update(r["batches"])
    return out


def nodes_for(batch) -> set[str]:
    b = _bn(batch)
    return {r["node"] for r in rows() if b in r["batches"]}


def decls_for(batch) -> set[str]:
    """the Lean declarations batch `batch` assumes (axioms of its sorry route)"""
    b = _bn(batch)
    return {d for r in rows() if b in r["batches"] for d in r["decls"]}


if __name__ == "__main__":
    print(f"# {path()}")
    for r in rows():
        print(r["node"], ",".join(sorted(r["batches"])), len(r["decls"]), "declarations:", " ".join(r["decls"]), sep="\t")
