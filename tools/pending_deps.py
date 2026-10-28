#!/usr/bin/env python3
"""Dependencies that passed review but have not landed yet (the owner, 2026-10-28: "允许审核通过后就放出下游任务，同时同步
给worker，让他们知道哪些文件是还没有通过入库的").

A delivery is PASSED, exactly as ~/cc1/queue_report.py counts it, when its group still holds the claim of the item and
  stage 3 (a module item): local/batch/passed/<G>__<item>.json has `head` equal to refs/heads/deliver/<G>/<item>,
                            or that head's set build passed (local/sets/passed/<head>.json, tools/setbuild.py, switch on);
  stage 1/2 (a node item):  local/verdicts/<stage>/<head>.json of that head says PASS.
Nothing weaker counts (a delivery under review, FIX, RETURN, an AUTO head nobody read).

What such a delivery provides before it lands (read from its branch against its merge base with the main branch):
  modules  the Lean modules it adds (lean/**.lean not on the main branch)
  nodes    the DAG nodes whose file on the branch carries a Lean record with a module (a statement it writes)
A module or node counts as pending only while the main branch does not have it (once it lands, the ordinary rules apply);
a node only when its module is one the delivery adds (a statement added to an existing module cannot be waited for as a
missing import, so it releases nothing early).

Used by
  tools/queue.py      (dag_queue.Dag.pending): a node stated by a passed delivery counts as available when releasing the
                      stage-2 items whose statement needs it and the stage-3 modules whose node depends on it; the items
                      released that way are written to coord/queue-pending-deps.tsv for the dispatcher's briefs;
  tools/quarantine_wait.py: a delivery importing a pending module (or one landed on the main branch but not in the
                      published build yet) waits instead of going back; if that dependency's delivery is returned or
                      replaced before it lands, the waiting delivery goes back to its writer with a note naming it;
  tools/review_class.py list: such a delivery is listed WAITDEPS (not CODEX) until its imports are in the published
                      build, so no reviewer reads a delivery it cannot compile;
  tools/batch_land.py: a delivery its tool pushed without a compile (report section PENDING_SECTION) is compiled alone
                      against the published build before it lands (tools/rework_fixcheck.compile_alone).

Cache: local/pending-deps/heads.json {head: {modules, nodes}} (a head's content never changes).
Usage: tools/pending_deps.py [show|modules|json]
  show     the passed, not landed deliveries and what they provide
  modules  one line per pending module: module <TAB> group <TAB> item <TAB> head   (read by deliver3.py)
  json     {"nodes": {...}, "modules": {...}}
"""
from __future__ import annotations
import json, os, pathlib, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
CACHE = ROOT / "local" / "pending-deps" / "heads.json"
MAIN = "sheaf-dag"
PENDING_SECTION = "## Pending dependencies (not compiled before delivery)"
_MEMO: dict = {}


def git(*a, check=False) -> str:
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if (r.returncode == 0 or not check) else ""


def claim_who(item: str):
    try:
        return json.loads((ROOT / "coord" / "claims" / f"{item}.lock").read_text()).get("who")
    except (OSError, ValueError):
        return None


def verdict(stage: str, head: str):
    try:
        return json.loads((ROOT / "local" / "verdicts" / stage / f"{head}.json").read_text()).get("verdict")
    except (OSError, ValueError):
        return None


def passed_marker(g: str, item: str, head: str) -> bool:
    try:
        return json.loads((ROOT / "local" / "batch" / "passed" / f"{g}__{item}.json").read_text()).get("head") == head
    except (OSError, ValueError):
        return False


def set_passed(g: str, item: str, head: str) -> bool:
    """2026-10-28 (the owner: a statement-preserving delivery is done when its set build passes): a passed set
    (tools/setbuild.py, switch `on`) counts as a pass here, so its dependents are released."""
    try:
        import setbuild
        return setbuild.is_passed(g, item, head)
    except Exception:  # noqa: BLE001
        return False


def queue_items() -> set[tuple[str, str]] | None:
    """(item, stage) of coord/queue.tsv, None when unreadable. Only an item the queue lists is counted (queue_report.py
    counts the queue's items): a passed stage-2 delivery of a node the queue no longer lists (below a written proof, not
    needed) is dropped by the review service and never lands, so nothing may wait for it."""
    try:
        rows = (ROOT / "coord" / "queue.tsv").read_text().splitlines()
    except OSError:
        return None
    out = {(p[0], p[1]) for l in rows if not l.startswith("#") and len(p := l.split("\t")) >= 2}
    return out or None


def heads() -> dict[tuple[str, str], str]:
    out = {}
    for line in git("for-each-ref", "--format=%(refname:short) %(objectname)", "refs/heads/deliver").splitlines():
        try:
            ref, h = line.split(" ")
        except ValueError:
            continue
        p = ref.split("/")
        if len(p) == 3:
            out[(p[1], p[2])] = h
    return out


def passed_stage(g: str, item: str, head: str, listed=None):
    """'3', '2' or '1' when this live head is passed (queue_report.py's definition: the item is on the queue at that
    stage, its group holds the claim, stage 3 pass marker of this head / stage 1-2 verdict PASS of this head), else None"""
    if claim_who(item) != g:
        return None
    if "." in item:
        st = "3" if passed_marker(g, item, head) or set_passed(g, item, head) else None
    else:
        st = next((x for x in ("2", "1") if verdict(x, head) == "PASS"), None)
    if st and listed is not None and (item, st) not in listed:
        return None
    return st


def _load_cache() -> dict:
    try:
        return json.loads(CACHE.read_text())
    except (OSError, ValueError):
        return {}


def _save_cache(data: dict) -> None:
    try:
        CACHE.parent.mkdir(parents=True, exist_ok=True)
        tmp = CACHE.with_name(CACHE.name + f".tmp{os.getpid()}")
        tmp.write_text(json.dumps(data))
        os.replace(tmp, CACHE)
    except OSError:
        pass


def _modname(path: str) -> str:
    return path[len("lean/"):-len(".lean")].replace("/", ".")


def provides(head: str) -> dict:
    """{modules: [new Lean modules], nodes: {node: module}} of the delivery commit `head` against its merge base"""
    base = git("merge-base", MAIN, head).strip()
    if not base:
        return {"modules": [], "nodes": {}}
    mods = [_modname(p) for p in git("diff", "--name-only", "--diff-filter=A", base, head, "--", "lean").split()
            if p.endswith(".lean") and "/.sandbox/" not in p and "/.lake/" not in p]
    nodes = {}
    for p in git("diff", "--name-only", "--diff-filter=AM", base, head, "--", "dag/nodes").split():
        if not p.endswith(".json"):
            continue
        try:
            d = json.loads(git("show", f"{head}:{p}"))
        except ValueError:
            continue
        rec = d.get("lean") if isinstance(d, dict) else None
        if isinstance(rec, dict) and rec.get("module") and d.get("id"):
            nodes[str(d["id"])] = str(rec["module"])
    return {"modules": sorted(mods), "nodes": nodes}


def on_main(module: str) -> bool:
    return (ROOT / "lean" / (module.replace(".", "/") + ".lean")).is_file()


def pending() -> dict:
    """{"nodes": {node: info}, "modules": {module: info}}, info = {group, item, head, stage, module}: what the passed,
    not landed deliveries provide. Memoized per process for 60 s."""
    hit = _MEMO.get("p")
    if hit and time.time() - hit[0] < 60:
        return hit[1]
    cache = _load_cache()
    live, changed = {}, False
    nodes, modules = {}, {}
    listed = queue_items()
    if listed is None:   # no queue read: nothing counts (never release work on a dependency that may not land)
        return {"nodes": {}, "modules": {}}
    for (g, item), h in sorted(heads().items()):
        st = passed_stage(g, item, h, listed)
        if not st:
            continue
        pv = cache.get(h)
        if pv is None:
            pv = provides(h); changed = True
        live[h] = pv
        for m in pv["modules"]:
            if not on_main(m):
                modules.setdefault(m, {"group": g, "item": item, "head": h, "stage": st, "module": m})
        for n, m in pv["nodes"].items():
            # only a statement in a NEW module of the delivery: its dependents import that module, and their deliveries wait
            # for it as a missing import (quarantine_wait.py); a statement added to an existing module could not be waited
            # for that way (the module exists, the declaration does not), so it releases nothing before it lands
            if m in pv["modules"] and not on_main(m):
                nodes.setdefault(n, {"group": g, "item": item, "head": h, "stage": st, "module": m})
    if changed or set(cache) - set(live):
        _save_cache(live)   # heads that are no longer passed drop out of the cache
    out = {"nodes": nodes, "modules": modules}
    _MEMO["p"] = (time.time(), out)
    return out


def published_commit() -> str:
    try:
        return json.loads((ROOT / "local" / "builds" / "published.json").read_text()).get("commit") or ""
    except (OSError, ValueError):
        return ""


def published_modules() -> set[str] | None:
    """the modules of the last published build (None when unknown)"""
    c = published_commit()
    if not c:
        return None
    hit = _MEMO.get("pub")
    if hit and hit[0] == c:
        return hit[1]
    paths = git("ls-tree", "-r", "--name-only", c, "--", "lean").split()
    s = {_modname(p) for p in paths if p.endswith(".lean")} if paths else None
    if s is not None:
        _MEMO["pub"] = (c, s)
    return s


def dep_state(dep: str) -> str:
    """for an import `dep` of a waiting delivery: 'published' (in the published build), 'landed' (on the main branch, not
    built yet), 'pending' (provided by a passed delivery that has not landed), 'gone' (none of these)"""
    pub = published_modules()
    if pub is not None and dep in pub:
        return "published"
    if on_main(dep):
        return "landed" if pub is not None else "published"
    if dep in pending()["modules"]:
        return "pending"
    return "gone"


def unbuilt_imports(texts: dict) -> list[tuple[str, str]]:
    """(module, import) for the imports of the delivered `texts` ({module: text or None}) that are neither delivered with
    them nor in the published build, but are pending or landed-not-built (dep_state): what such a delivery waits for"""
    import import_cycles as ic
    out = []
    for m, t in sorted(texts.items()):
        if t is None:
            continue
        for d in sorted(ic.imports(t)):
            if d in texts or not (d.startswith("Sheaf.") or d.startswith("WeilConjectures.")):
                continue
            if dep_state(d) in ("pending", "landed"):
                out.append((m, d))
    return out


def compile_check(head: str, texts: dict) -> tuple[str, str]:
    """A delivery pushed without a compile because a dependency had not landed (its report has PENDING_SECTION): each
    delivered module that imports no other delivered module, compiled alone against the published build
    (tools/rework_fixcheck.compile_alone: -j1, LEAN_NUM_THREADS=1, the 60 s rule). ('ok'|'error'|'missing'|'infra', out);
    results cached per head and text in local/pending-deps/compiled.json."""
    import hashlib
    import import_cycles as ic
    import rework_fixcheck as rfc
    f = CACHE.with_name("compiled.json")
    try:
        done = json.loads(f.read_text())
    except (OSError, ValueError):
        done = {}
    names = {m for m, t in texts.items() if t is not None}
    for m, t in sorted(texts.items()):
        if t is None or any(d in names and d != m for d in ic.imports(t)):
            continue   # a module importing a sibling of the delivery: the global build compiles it with the set
        key = f"{head}:{m}:{hashlib.sha1(t.encode()).hexdigest()}"
        if done.get(key) == "ok":
            continue
        st, out = rfc.compile_alone(m, t)
        if st != "ok":
            return st, f"{m}: {out[-3000:]}"
        done[key] = "ok"
        try:
            f.parent.mkdir(parents=True, exist_ok=True)
            tmp = f.with_name(f.name + f".tmp{os.getpid()}"); tmp.write_text(json.dumps(done)); os.replace(tmp, f)
        except OSError:
            pass
    return "ok", ""


def ref_of(info: dict) -> str:
    return f"deliver/{info['group']}/{info['item']}"


def main() -> int:
    cmd = sys.argv[1] if len(sys.argv) > 1 else "show"
    p = pending()
    if cmd == "json":
        print(json.dumps(p))
    elif cmd == "modules":
        for m, i in sorted(p["modules"].items()):
            print(f"{m}\t{i['group']}\t{i['item']}\t{i['head']}")
    elif cmd == "show":
        by = {}
        for kind in ("modules", "nodes"):
            for k, i in p[kind].items():
                by.setdefault((i["group"], i["item"], i["head"], i["stage"]), {"modules": [], "nodes": []})[kind].append(k)
        for (g, it, h, st), v in sorted(by.items()):
            print(f"{g}\t{it}\tstage {st}\t{h[:9]}\tmodules {', '.join(sorted(v['modules'])) or '-'}\tnodes {', '.join(sorted(v['nodes'])) or '-'}")
        print(f"{len(by)} passed deliveries not landed; {len(p['modules'])} pending modules, {len(p['nodes'])} pending node statements")
    else:
        print(__doc__); return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
