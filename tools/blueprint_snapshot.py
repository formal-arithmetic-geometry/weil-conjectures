#!/usr/bin/env python3
"""Bring a new snapshot of the blueprint (formal-arithmetic-geometry/weil-conjectures-blueprint, branch main) into the
project, the way the snapshots of 2026-10-15 (imported 2026-10-16, e7ca1a8cf6, be148130e2, 6d63bf6ef7) and 2026-10-17
(df19dd5c27) were brought in. Run by ~/cc1/blueprint-refresh.sh every day; by hand:

  tools/blueprint_snapshot.py install --clone DIR [--commit REV] [--name main-YYYYMMDD] [--dest DIR]
        export REV (default origin/main) of the blueprint clone DIR into literature/blueprint/<name> (no .git) and add
        the line `<name> <sha> (weil-conjectures-blueprint main, <commit time UTC>; <subject>)` to COMMITS.txt
  tools/blueprint_snapshot.py latest
        print the name and commit of the newest main-* snapshot recorded in COMMITS.txt
  tools/blueprint_snapshot.py merge --snapshot NAME [--base NAME] [--snapshot-dir DIR] [--dry] [--report FILE]
        import the snapshot into dag/nodes (the base defaults to the snapshot recorded before it in COMMITS.txt)

What `merge` does (no node is ever deleted, no status is changed, no Lean file is read or written except through
tools/live_closed.py for the "proved" count):
  1. both snapshots are imported with tools/import_blueprint.py into a scratch root (~/cc1/blueprint-refresh/import),
     each `X.proof.md` (kind proof, of = X) supplying the `## Proof` of X and its `uses`;
  2. a blueprint node whose id is not in dag/nodes is added as imported (status imported/unsplit as the import says,
     `blueprint_snapshot`, `blueprint` = {is: id, from: null, same_as: null}, chapter and unit; the unit and chapter
     records of new sketch units are written, existing chapter records are kept);
  3. an existing node whose blueprint statement or proof changed between the base and the snapshot (a statement equal
     to the node's own current statement is not a change) gets `blueprint_update` = {snapshot, commit, changed,
     statement, proof, note}; its own fields stay as they are, a worker who touches it follows the update. A node
     proved in Lean (tools/dag_queue.py finished) is recorded the same way and never reopened; the report lists those
     whose statement changed, for the human to judge;
  4. blueprint nodes of the base that the snapshot no longer has are only counted (nodes are never deleted);
  5. one commit under flock coord/.merge.lock (SHEAF_LEAD=L-only) with only these files.
"""
from __future__ import annotations
import argparse, datetime, fcntl, json, os, pathlib, re, shutil, subprocess, sys

TOOLS = pathlib.Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
LIT = ROOT / "literature" / "blueprint"
COMMITS = LIT / "COMMITS.txt"
WORK = pathlib.Path(os.environ.get("BLUEPRINT_REFRESH_WORK", pathlib.Path.home() / "cc1" / "blueprint-refresh"))
NODES = ROOT / "dag" / "nodes"
TRAILER = "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
FM = re.compile(r"\+\+\+\n(.*?)\n\+\+\+\n?(.*)", re.S)


def say(*a):
    print(time_stamp(), *a, flush=True)


def time_stamp():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%FT%TZ")


def dump(d: dict) -> str:
    return json.dumps(d, indent=1, ensure_ascii=False) + "\n"


# ------------------------------------------------------------------------------------------------ snapshots
def recorded() -> list[tuple[str, str]]:
    out = []
    for line in COMMITS.read_text().splitlines():
        p = line.split()
        if len(p) >= 2 and p[0].startswith("main-"):
            out.append((p[0], p[1]))
    return out


def install(a) -> int:
    clone = pathlib.Path(a.clone)
    sha = subprocess.run(["git", "-C", clone, "rev-parse", a.commit], capture_output=True, text=True, check=True).stdout.strip()
    info = subprocess.run(["git", "-C", clone, "show", "-s", "--format=%ct%x00%s", sha], capture_output=True, text=True,
                          check=True).stdout.strip().split("\0")
    when = datetime.datetime.fromtimestamp(int(info[0]), datetime.timezone.utc).strftime("%FT%H:%MZ")
    for name, c in recorded():
        if c == sha:
            say(f"{sha[:10]} is already installed as {name}")
            print(f"INSTALLED {name} {sha}")
            return 0
    name = a.name or "main-" + datetime.date.today().strftime("%Y%m%d")
    taken = {n for n, _ in recorded()}
    if name in taken or (LIT / name).exists():
        name = name + "-" + datetime.datetime.now().strftime("%H%M")
    dest = pathlib.Path(a.dest) / name if a.dest else LIT / name
    if dest.exists():
        raise SystemExit(f"{dest} exists")
    tmp = dest.with_name(dest.name + ".partial")
    if tmp.exists():
        shutil.rmtree(tmp)
    tmp.mkdir(parents=True)
    arch = subprocess.run(["git", "-C", clone, "archive", "--format=tar", sha], capture_output=True, check=True).stdout
    subprocess.run(["tar", "-x", "-C", tmp], input=arch, check=True)
    tmp.rename(dest)
    line = f"{name} {sha} (weil-conjectures-blueprint main, {when}; {info[1]})\n"
    if not a.dest:
        with COMMITS.open("a") as f:
            f.write(line)
    say(f"installed {sha[:10]} as {dest}")
    print(f"INSTALLED {name} {sha}")
    return 0


# ------------------------------------------------------------------------------------------------ import
def frontmatter_lines(text: str):
    m = FM.match(text)
    if not m:
        return None, text
    return m.group(1).splitlines(), m.group(2)


def fm_value(lines, key):
    for ln in lines:
        k, _, v = ln.partition("=")
        if k.strip() == key:
            v = v.strip()
            if v.startswith("["):
                return re.findall(r'"((?:[^"\\]|\\.)*)"', v)
            if v.startswith('"'):
                return json.loads(v)
            return v
    return None


def prepared_tree(bp: pathlib.Path, root: pathlib.Path, name: str) -> pathlib.Path:
    """root/literature/blueprint/<name>/blueprint: the .md files of bp, every `X.proof.md` folded into X as its
    `## Proof` (the `uses` of both kept), so that tools/import_blueprint.py reads one file per node."""
    out = root / "literature" / "blueprint" / name / "blueprint"
    if out.exists():
        shutil.rmtree(out)
    files, proofs, by_id = {}, [], {}
    for p in sorted(bp.rglob("*.md")):
        lines, body = frontmatter_lines(p.read_text())
        if lines is None:
            continue
        if fm_value(lines, "kind") == "proof":
            proofs.append((p, lines, body)); continue
        files[p] = [lines, body]
        i = fm_value(lines, "id")
        if i:
            by_id[i] = p
    orphan = []
    for p, lines, body in proofs:
        of = fm_value(lines, "of")
        target = p.with_name(p.name[: -len(".proof.md")] + ".md") if p.name.endswith(".proof.md") else None
        if target not in files:
            target = by_id.get(of)
        if target is None:
            orphan.append(str(p.relative_to(bp))); continue
        tl, tb = files[target]
        if re.search(r"^## Proof\s*$", tb, re.M) is None:
            tb = tb.rstrip("\n") + "\n\n## Proof\n\n" + body.strip("\n") + "\n"
        uses = list(dict.fromkeys((fm_value(tl, "uses") or []) + (fm_value(lines, "uses") or [])))
        tl = [ln for ln in tl if ln.partition("=")[0].strip() != "uses"]
        if uses:
            tl.append("uses = [" + ", ".join(json.dumps(u) for u in uses) + "]")
        files[target] = [tl, tb]
    for p, (lines, body) in files.items():
        q = out / p.relative_to(bp)
        q.parent.mkdir(parents=True, exist_ok=True)
        q.write_text("+++\n" + "\n".join(lines) + "\n+++\n" + body)
    if orphan:
        say(f"{name}: {len(orphan)} proof file(s) without their statement: {orphan[:5]}")
    return out


def import_snapshot(name: str, snapdir: pathlib.Path) -> dict[str, dict]:
    """id -> node as tools/import_blueprint.py makes it from the snapshot (scratch root, never dag/ of the project)."""
    root = WORK / "import" / name
    tree = prepared_tree(snapdir / "blueprint", root, name)
    import import_blueprint as ib
    ib.ROOT, ib.BP = root, tree
    argv = sys.argv
    sys.argv = ["import_blueprint.py", "--lean-master", "", "--lean-slopmaster2", "", "--mathlib", ""]
    try:
        import contextlib, io
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            ib.main()
        (root / "import-report.json").write_text(buf.getvalue())
    finally:
        sys.argv = argv
    out = {}
    for p in (root / "dag" / "nodes").rglob("*.json"):
        d = json.loads(p.read_text())
        d["_section"] = p.parent.name
        out[d["id"]] = d
    return out


def norm(s) -> str:
    return " ".join(str(s or "").split())


def proof_text(d: dict) -> str:
    if d.get("proof"):
        return "\n\n".join(s.get("text", "") for s in d["proof"])
    return d.get("blueprint_proof_text") or ""


# ------------------------------------------------------------------------------------------------ merge
def live_nodes() -> dict[str, pathlib.Path]:
    return {p.stem: p for p in NODES.glob("*/*.json")}


def proved_set(ids) -> tuple[set, set]:
    """(proved in Lean, stated in Lean) among ids, by tools/dag_queue.py"""
    import dag_queue as dq
    nodes = dq.load()
    try:
        dq.Dag(nodes)            # sets up the assumed nodes the batches assume
    except Exception as e:       # noqa: BLE001
        say("dag_queue.Dag failed, assumed nodes not counted:", repr(e)[:200])
    proved, stated = set(), set()
    for i in ids:
        d = nodes.get(i)
        if d is None:
            continue
        try:
            if dq.finished(d):
                proved.add(i)
            if dq.stated_node(d):
                stated.add(i)
        except Exception as e:   # noqa: BLE001
            say(f"dag_queue on {i} failed: {e!r}"[:200])
    return proved, stated


def plan(snapshot: str, base: str, snapdir: pathlib.Path, commit: str) -> dict:
    say(f"importing {snapshot} and its base {base}")
    new = import_snapshot(snapshot, snapdir)
    old = import_snapshot(base, LIT / base)
    files = live_nodes()
    added, changed, gone = [], {}, sorted(set(old) - set(new))
    for i, n in new.items():
        if i not in files:
            added.append(i); continue
        live = json.loads(files[i].read_text())
        o = old.get(i)
        what = []
        if o is not None:
            if norm(n["statement"]) != norm(o["statement"]) and norm(n["statement"]) != norm(live.get("statement")):
                what.append("statement")
            if norm(proof_text(n)) != norm(proof_text(o)):
                what.append("proof")
        else:   # a node of ours that the blueprint now has (or one from an older snapshot): compare with the node itself
            if norm(n["statement"]) != norm(live.get("statement")):
                what.append("statement")
        if what:
            changed[i] = what
    proved, stated = proved_set(changed)
    # renamed: an added id whose statement is the statement of a node the snapshot dropped
    gone_stmt = {norm(old[g]["statement"]): g for g in gone}
    renamed = {i: gone_stmt[norm(new[i]["statement"])] for i in added if norm(new[i]["statement"]) in gone_stmt}
    return {"snapshot": snapshot, "commit": commit, "base": base, "new": new, "old": old, "added": sorted(added),
            "changed": changed, "proved": proved, "stated": stated, "gone": gone, "renamed": renamed}


def write_units(snapdir: pathlib.Path, new_nodes: list[str]) -> list[pathlib.Path]:
    """unit and chapter records of the sketch units the DAG has no record of (tools/units.py build --snapshot, existing
    chapter records kept), then units.stamp_missing on the new nodes. Returns the files written."""
    import units as U
    bp = snapdir / "blueprint"
    have = {p.stem for p in U.UNITS.glob("*.json")}
    want = sorted(sk.name for sec in bp.glob("sec-*") for sk in sec.glob("sk-*")
                  if (sk / "_section.md").is_file() and sk.name not in have)
    written = []
    if want:
        keep = {p: p.read_bytes() for p in U.CHAPTERS.glob("*.json")}
        before = set(ROOT.joinpath("dag").rglob("*.bak"))
        U.build(bp, set(want))
        for p, b in keep.items():
            p.write_bytes(b)
        for p in set(ROOT.joinpath("dag").rglob("*.bak")) - before:
            p.unlink()
        written += [U.UNITS / f"{u}.json" for u in want]
        written += [p for p in U.CHAPTERS.glob("*.json") if p not in keep]
    units, chapters = U.load_units()
    files = live_nodes()
    for i in new_nodes:
        d = json.loads(files[i].read_text())
        t = dump(d)
        U.stamp_missing(d, units, chapters)
        if dump(d) != t:
            files[i].write_text(dump(d))
    return written, want


def break_cycles(snap: str) -> list[pathlib.Path]:
    """The rules of the 2026-10-16 import (04c6a14b28, 6cb3c794dc), applied only to nodes this snapshot added: inside a
    dependency cycle, a sketch node (`_section.md` of a unit) no longer lists a detail node of its own unit (kept in
    `blueprint_detail_nodes`), and a node no longer lists a later blueprint node (larger blueprint_order; kept in
    `blueprint_forward_refs`)."""
    from check_dag import sccs
    files = live_nodes()
    nodes = {i: json.loads(p.read_text()) for i, p in files.items()}
    mine = {i for i, d in nodes.items() if d.get("blueprint_snapshot") == snap}
    changed = set()
    for _ in range(50):
        graph = {i: list(dict.fromkeys((d.get("stmt_deps") or []) + (d.get("proof_deps") or []))) for i, d in nodes.items()}
        cyc = [c for c in sccs(graph) if len(c) > 1 and set(c) & mine]
        if not cyc:
            break
        progress = False
        for c in cyc:
            cs = set(c)
            for u in sorted(cs & mine):
                d = nodes[u]
                udoc = str((d.get("source") or {}).get("document") or "")
                for v in [x for x in graph[u] if x in cs]:
                    vdoc = str((nodes[v].get("source") or {}).get("document") or "")
                    detail = udoc.endswith("/_section.md") and vdoc.startswith(udoc[: -len("_section.md")])
                    forward = (nodes[v].get("blueprint_order") or -1) > (d.get("blueprint_order") or 10 ** 9)
                    if not (detail or forward):
                        continue
                    key = "blueprint_detail_nodes" if detail else "blueprint_forward_refs"
                    d[key] = list(dict.fromkeys((d.get(key) or []) + [v]))
                    for f in ("stmt_deps", "proof_deps"):
                        d[f] = [x for x in d.get(f) or [] if x != v]
                    for s in d.get("proof") or []:
                        s["uses"] = [x for x in s.get("uses") or [] if x != v]
                    changed.add(u); progress = True
                    break
                if progress:
                    break
            if progress:
                break
        if not progress:
            break
    for u in changed:
        files[u].write_text(dump(nodes[u]))
    return [files[u] for u in changed]


def apply(P: dict, snapdir: pathlib.Path) -> list[pathlib.Path]:
    snap, commit = P["snapshot"], P["commit"]
    today = datetime.date.today().isoformat()
    files = live_nodes()
    touched = []
    for i in P["added"]:
        if i in files:          # appeared meanwhile: never overwrite
            continue
        n = dict(P["new"][i])
        sec = n.pop("_section")
        n["blueprint_snapshot"] = snap
        n["blueprint"] = {"is": i, "from": None, "same_as": None}
        out = NODES / sec / f"{i}.json"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(dump(n))
        touched.append(out)
    note = (f"the current blueprint ({snap}, weil-conjectures-blueprint {commit[:10]}) states or proves this differently; "
            "a worker who touches the node follows it")
    for i, what in P["changed"].items():
        p = files[i]
        d = json.loads(p.read_text())
        n = P["new"][i]
        u = {"snapshot": snap, "commit": commit, "changed": what, "statement": n["statement"], "proof": n["proof"],
             "note": note}
        if not n["proof"] and n.get("blueprint_proof_text"):
            u["proof_text"] = n["blueprint_proof_text"]
        if i in P["proved"]:
            u["note"] = note.replace("a worker who touches the node follows it",
                                     f"the node is proved in Lean: recorded {today}, not reopened")
        if d.get("blueprint_update") == u:
            continue
        d["blueprint_update"] = u
        p.write_text(dump(d))
        touched.append(p)
    written, units = write_units(snapdir, [i for i in P["added"]])
    P["units_added"] = units
    P["cycle_breaks"] = sorted(p.stem for p in break_cycles(snap))
    return touched + written


def summary(P: dict) -> dict:
    ch = P["changed"]
    stmt = [i for i, w in ch.items() if "statement" in w]
    return {
        "snapshot": P["snapshot"], "commit": P["commit"], "base": P["base"],
        "blueprint_nodes": len(P["new"]),
        "new_nodes": len(P["added"]),
        "new_nodes_by_status": dict(sorted(__import__("collections").Counter(P["new"][i]["status"] for i in P["added"]).items())),
        "new_nodes_renamed_from": P["renamed"],
        "changed_nodes": len(ch),
        "changed_statement": len(stmt),
        "changed_proof_only": sum(1 for w in ch.values() if w == ["proof"]),
        "changed_proved_in_lean": sorted(i for i in ch if i in P["proved"]),
        "changed_statement_proved_in_lean": sorted(i for i in stmt if i in P["proved"]),
        "changed_statement_stated_in_lean_not_proved": sorted(i for i in stmt if i in P["stated"] and i not in P["proved"]),
        "reopened": [],
        "dropped_from_blueprint": len(P["gone"]),
        "dropped_from_blueprint_ids": P["gone"],
        "units_added": P.get("units_added", []),
        "cycle_breaks": P.get("cycle_breaks", []),
        "changed": ch,
    }


def lock_and_commit(paths: list[pathlib.Path], msg: str) -> str:
    rel = sorted({str(p.relative_to(ROOT)) for p in paths})
    env = dict(os.environ, SHEAF_LEAD="L-only")
    lst = WORK / "commit-paths.txt"
    lst.write_text("\n".join(rel) + "\n")
    git = ["git", "-C", str(ROOT)]
    subprocess.run(git + ["add", "--pathspec-from-file", str(lst)], check=True, env=env)
    subprocess.run(git + ["-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m", msg,
                          "--pathspec-from-file", str(lst)], check=True, env=env)
    return subprocess.run(git + ["rev-parse", "--short=11", "HEAD"], capture_output=True, text=True).stdout.strip()


def merge(a) -> int:
    snap = a.snapshot
    rec = dict(recorded())
    names = [n for n, _ in recorded()]
    snapdir = pathlib.Path(a.snapshot_dir) if a.snapshot_dir else LIT / snap
    if not snapdir.is_dir():
        raise SystemExit(f"no snapshot {snapdir}")
    if a.snapshot_dir and not a.dry:
        raise SystemExit("--snapshot-dir only with --dry: the nodes' sources must point into literature/blueprint")
    commit = a.commit or rec.get(snap, "")
    if a.base:
        base = a.base
    elif snap in names:
        base = names[names.index(snap) - 1] if names.index(snap) > 0 else None
    else:
        base = names[-1] if names else None
    if not base:
        raise SystemExit("no base snapshot")
    WORK.mkdir(parents=True, exist_ok=True)
    P = plan(snap, base, snapdir, commit)
    if a.dry:
        s = summary(P)
        (pathlib.Path(a.report) if a.report else WORK / f"report-{snap}-dry.json").write_text(json.dumps(s, indent=1, ensure_ascii=False) + "\n")
        print(json.dumps({k: v for k, v in s.items() if k not in ("changed", "dropped_from_blueprint_ids")}, indent=1, ensure_ascii=False))
        return 0
    lock = open(ROOT / "coord" / ".merge.lock", "a")
    say("waiting for coord/.merge.lock")
    fcntl.flock(lock, fcntl.LOCK_EX)
    try:
        # the live nodes may have moved while the imports ran: decide again on the current files
        files = live_nodes()
        P["added"] = [i for i in P["added"] if i not in files]
        touched = apply(P, snapdir)
        s = summary(P)
        if not touched:
            say("nothing to commit")
            sha = None
        else:
            msg = (f"Blueprint main {commit[:9]}: snapshot literature/blueprint/{snap} into the DAG: {s['new_nodes']} new nodes "
                   f"imported, {s['changed_nodes']} nodes whose blueprint text changed carry blueprint_update\n\n"
                   f"Base {base}. Statement changed: {s['changed_statement']} (of them proved in Lean, recorded and not "
                   f"reopened: {len(s['changed_statement_proved_in_lean'])}); proof only: {s['changed_proof_only']}. "
                   f"Blueprint nodes the snapshot dropped (kept in the DAG): {s['dropped_from_blueprint']}. New units: "
                   f"{len(s['units_added'])}. tools/blueprint_snapshot.py merge.\n\n{TRAILER}")
            sha = lock_and_commit(touched, msg)
            say(f"committed {sha}: {len(touched)} files")
        s["dag_commit"] = sha
    finally:
        fcntl.flock(lock, fcntl.LOCK_UN)
    (pathlib.Path(a.report) if a.report else WORK / f"report-{snap}.json").write_text(json.dumps(s, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps({k: v for k, v in s.items() if k not in ("changed", "dropped_from_blueprint_ids")}, indent=1, ensure_ascii=False))
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    i = sub.add_parser("install")
    i.add_argument("--clone", required=True)
    i.add_argument("--commit", default="origin/main")
    i.add_argument("--name")
    i.add_argument("--dest", help="install here instead of literature/blueprint (a dry run); COMMITS.txt untouched")
    sub.add_parser("latest")
    m = sub.add_parser("merge")
    m.add_argument("--snapshot", required=True)
    m.add_argument("--base")
    m.add_argument("--snapshot-dir")
    m.add_argument("--commit")
    m.add_argument("--dry", action="store_true")
    m.add_argument("--report")
    c = sub.add_parser("cycles", help="break the cycles of nodes a snapshot added (merge does it; for an earlier merge)")
    c.add_argument("--snapshot", required=True)
    a = ap.parse_args()
    if a.cmd == "cycles":
        lock = open(ROOT / "coord" / ".merge.lock", "a")
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            touched = break_cycles(a.snapshot)
            if touched:
                sha = lock_and_commit(touched, f"Break the dependency cycles of the {a.snapshot} blueprint import (rules of "
                                      f"the 2026-10-16 import: a sketch no longer lists its own detail nodes inside a cycle, "
                                      f"kept in blueprint_detail_nodes; forward references inside a cycle kept in "
                                      f"blueprint_forward_refs): {', '.join(sorted(p.stem for p in touched))}\n\n{TRAILER}")
                say(f"committed {sha}")
            else:
                say("no cycle to break")
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)
        return 0
    if a.cmd == "install":
        return install(a)
    if a.cmd == "latest":
        n, c = recorded()[-1]
        print(n, c); return 0
    return merge(a)


if __name__ == "__main__":
    sys.exit(main())
