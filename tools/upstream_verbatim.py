#!/usr/bin/env python3
"""Upstream files verbatim (the human, 2026-10-20): every file of the source library in lean/ that differs from the
source's tip takes the tip's text. What only our version had moves out of the upstream file:

  * a declaration the tip does not have goes to a companion module of ours,
    lean/Sheaf/UpstreamExtra/<the upstream path>.lean (module Sheaf.UpstreamExtra.<upstream module>), which imports
    the tip's file and keeps our file's context (namespaces, open, variable, other commands) without the declarations
    the tip has; our modules that import the upstream file and name one of those declarations import the companion
    too, and the DAG nodes recording them point at it;
  * a proof of ours of a declaration whose tip body is only `sorry`, with the same statement, is kept (filling an
    upstream sorry is the one change of an upstream file allowed in live).

Files listed in coord/upstream-statement-exceptions.tsv keep our version. Upstream files we deleted stay deleted, and
lean/WeilConjectures.lean takes the tip's text without the imports of modules not in lean/. What does not compile
afterwards (a private helper of the upstream file, a changed context) goes through the sync's quarantine.

  tools/upstream_verbatim.py <tip> --source-git DIR [--dry-run] [--json OUT]
"""
from __future__ import annotations
import collections, json, pathlib, re, subprocess, sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402
import stage2_delivery as s2  # noqa: E402

ROOT = li.ROOT
EXTRA = "Sheaf.UpstreamExtra"
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)


def exceptions() -> set[str]:
    p = ROOT / "coord" / "upstream-statement-exceptions.tsv"
    return {l.split("\t")[0] for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")} if p.exists() else set()


def tip_files(up: str, tip: str) -> dict[str, str]:
    out = {}
    for l in subprocess.run(["git", "-C", up, "ls-tree", "-r", tip], capture_output=True, text=True, check=True).stdout.splitlines():
        meta, p = l.split("\t", 1)
        if p.endswith(".lean") and p.startswith("WeilConjectures"):
            out[p] = meta.split()[2]
    return out


def blobs(up: str, shas: list[str]) -> dict[str, bytes]:
    if not shas:
        return {}
    r = subprocess.run(["git", "-C", up, "cat-file", "--batch"], input="".join(s + "\n" for s in shas).encode(),
                       capture_output=True, check=True).stdout
    out, off = {}, 0
    for s in shas:
        e = r.index(b"\n", off); size = int(r[off:e].split()[2])
        out[s] = r[e + 1:e + 1 + size]; off = e + size + 2
    return out


def key(d) -> str:
    return d["name"] or "instance " + " ".join((d["statement"] or "").split())


def span(text: str, d) -> tuple[int, int]:
    """[start, end) of a declaration with its docstring"""
    s = d["start"]
    before = text[:s].rstrip()
    if d.get("docstring") and before.endswith("-/"):
        o = before.rfind("/--")
        if o >= 0:
            s = o
    return s, d["end"]


def only_sorry(body: str) -> bool:
    return re.sub(r"\s+", " ", re.sub(r"^:=\s*(by\s+)?", "", body.strip())).strip() in ("sorry", "by sorry")


def companion(mod: str, ours: str, extra_keys: set[str], decl_o) -> str:
    """our file without the declarations the tip has, importing the tip's module"""
    cut = sorted(span(ours, d) for d in decl_o if key(d) not in extra_keys)
    keep, pos = [], 0
    for s, e in cut:
        if s >= pos:
            keep.append(ours[pos:s]); pos = e
    keep.append(ours[pos:])
    body = "".join(keep)
    lines = body.split("\n")
    head_end = max((i + 1 for i, l in enumerate(lines) if IMPORT.match(l)), default=0)   # after the last import
    imports = [m for m in IMPORT.findall("\n".join(lines[:head_end])) if m != mod]
    rest = "\n".join(lines[head_end:])
    return ("module\n\n" + f"public import {mod}\n" + "".join(f"public import {m}\n" for m in imports)
            + f"\n/-! Declarations of ours that lived in the upstream file `{mod}` (moved out by the scheduled sync, "
              "tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/\n\n" + rest.lstrip("\n"))


def run(tip: str, up: str, write: bool = True) -> dict:
    exc = exceptions()
    tf = tip_files(up, tip)
    live = {str(p.relative_to(li.LEAN)): p for p in (li.LEAN / "WeilConjectures").rglob("*.lean")}
    root = li.LEAN / "WeilConjectures.lean"
    cand = []
    for rel, p in sorted(live.items()):
        if rel in tf and rel[:-5].replace("/", ".") not in exc:
            cand.append(rel)
    tipb = blobs(up, [tf[r] for r in cand] + ([tf["WeilConjectures.lean"]] if "WeilConjectures.lean" in tf else []))
    prev: dict[str, bytes | None] = {}
    moved: dict[str, dict[str, str]] = {}      # upstream module -> {declaration key: companion module}
    fills = 0
    stats = collections.Counter()
    for rel in cand:
        p = live[rel]
        ours_b = p.read_bytes(); t_b = tipb[tf[rel]]
        if ours_b == t_b:
            continue
        mod = rel[:-5].replace("/", ".")
        ours, tipt = ours_b.decode(errors="replace"), t_b.decode(errors="replace")
        try:
            do, dt = s2.declarations(ours), s2.declarations(tipt)
        except Exception:   # noqa: BLE001
            stats["unparsed"] += 1; do, dt = [], []
        tkeys = {key(d): d for d in dt}
        extra = {key(d) for d in do if key(d) not in tkeys}
        # our proofs of the tip's sorried declarations, same statement
        new = tipt
        ok = {key(d): d for d in do}
        xshort = {k.split(".")[-1] for k in extra if not k.startswith("instance ")}
        for d in sorted(dt, key=lambda d: d["start"], reverse=True):
            o = ok.get(key(d))
            body_o = ours[o["start"]:o["end"]] if o else ""
            if o and only_sorry(d["body"]) and not only_sorry(o["body"]) and \
                    " ".join((o["statement"] or "").split()) == " ".join((d["statement"] or "").split()) and \
                    not any(re.search(r"(?<![\w'])" + re.escape(n) + r"(?![\w'])", body_o) for n in xshort):
                # (a proof that uses a declaration moved to the companion cannot stay in the upstream file)
                new = new[:d["start"]] + ours[o["start"]:o["end"]] + new[d["end"]:]
                fills += 1
        prev[rel] = ours_b
        stats["to tip"] += 1
        if write:
            p.write_text(new)
        if extra:
            cmod = f"{EXTRA}.{mod}"
            crel = cmod.replace(".", "/") + ".lean"
            prev.setdefault(crel, (li.LEAN / crel).read_bytes() if (li.LEAN / crel).is_file() else None)
            if write:
                (li.LEAN / crel).parent.mkdir(parents=True, exist_ok=True)
                (li.LEAN / crel).write_text(companion(mod, ours, extra, do))
            moved[mod] = {k: cmod for k in extra}
            stats["companions"] += 1
    # the source root: the tip's text, without imports of modules not in lean/
    if "WeilConjectures.lean" in tf:
        rt = tipb[tf["WeilConjectures.lean"]].decode(errors="replace")
        rt = "\n".join(l for l in rt.split("\n") if not (IMPORT.match(l) and not li.file_of(IMPORT.match(l).group(1)).is_file()
                                                          and IMPORT.match(l).group(1).startswith("WeilConjectures")))
        if root.read_text() != rt:
            prev["WeilConjectures.lean"] = root.read_bytes()
            if write:
                root.write_text(rt)
    # our consumers of the moved declarations import the companion
    consumers = 0
    if moved:
        names = {mod: {k.split(".")[-1] for k in ks if not k.startswith("instance ")} for mod, ks in moved.items()}
        files = list((li.LEAN / "Sheaf").rglob("*.lean")) + [li.LEAN / "TargetsCheck.lean"]
        for f in files:
            rel = str(f.relative_to(li.LEAN))
            if rel.startswith("Sheaf/UpstreamExtra/"):
                continue
            try:
                t = f.read_text()
            except OSError:
                continue
            ims = set(IMPORT.findall(t))
            add = []
            for mod, ns in names.items():
                if mod in ims and (not ns or any(re.search(r"(?<![\w'])" + re.escape(n) + r"(?![\w'])", t) for n in ns)):
                    add.append(f"{EXTRA}.{mod}")
            add = [a for a in add if a not in ims]
            if add:
                lines = t.split("\n")
                last = max(i for i, l in enumerate(lines) if IMPORT.match(l))
                lines[last + 1:last + 1] = [f"public import {a}" for a in add]
                prev.setdefault(rel, t.encode()); consumers += 1
                if write:
                    f.write_text("\n".join(lines))
    # DAG nodes recording a moved declaration
    nodes = []
    for p in sorted((ROOT / "dag" / "nodes").glob("*/*.json")):
        t = p.read_text()
        if '"WeilConjectures.' not in t:
            continue
        try:
            n = json.loads(t)
        except ValueError:
            continue
        l = n.get("lean")
        if not isinstance(l, dict) or l.get("module") not in moved:
            continue
        ds = [l.get("declaration")] + list(l.get("declarations") or [])
        ds = [d.get("name") if isinstance(d, dict) else d for d in ds if d]
        if any(d in moved[l["module"]] for d in ds):
            cm = f"{EXTRA}.{l['module']}"
            l["module"] = cm
            if "file" in l:
                l["file"] = "lean/" + cm.replace(".", "/") + ".lean"
            nodes.append(str(p.relative_to(ROOT)))
            if write:
                p.write_text(json.dumps(n, ensure_ascii=False, indent=1) + "\n")
    return {"lean": prev, "nodes": nodes, "moved": {m: sorted(v) for m, v in moved.items()}, "fills": fills,
            "consumers": consumers, "stats": dict(stats)}


def main() -> int:
    a = sys.argv[1:]
    tip = a[0]; up = a[a.index("--source-git") + 1]
    r = run(tip, up, write="--dry-run" not in a)
    if "--json" in a:
        pathlib.Path(a[a.index("--json") + 1]).write_text(json.dumps({k: v for k, v in r.items() if k != "lean"}, indent=1))
    print(f"upstream verbatim: {r['stats']}; {sum(len(v) for v in r['moved'].values())} declarations of ours moved to "
          f"{len(r['moved'])} companion modules; {r['fills']} proofs of upstream sorries kept; {r['consumers']} consumers "
          f"import a companion; {len(r['nodes'])} DAG nodes re-pointed" + (" (dry run)" if "--dry-run" in a else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
