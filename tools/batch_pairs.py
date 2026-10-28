#!/usr/bin/env python3
"""Two deliveries of ONE batch that depend on each other are compiled together before the batch lands (2026-10-28).

Why: red build 375085fafa (08:56 CST, batch 20261027T233735). E5 (b7d022e7caf, NativeWeilTensorRingedChainData) added a
hypothesis `hsign` to `native_weil_tensor_ringed_chain_data`; its related-modules recheck (tools/importer_compile.py)
found no related module, because on main the user Sheaf.Paper.NativeWeilTensorRingedKFlatFlat was still a sorry stub
without that import. K8 (the KFlatFlat proof, importing ChainData) landed 90 s later in the same batch and the global
build failed. The recheck reads only the importers on main, never the other deliveries of the batch.

What (tools/batch_land.py land_batch calls split() on the checked stage-3 plans, before anything is written):
  1. Links. For each delivery A, tools/related_modules.py related() of A's changes in the graph of the batch's combined
     state (main + every delivery of the batch), reading only the texts delivered in the batch: a delivered module of
     another delivery B is linked when it is a direct importer of a module whose interface A changes, or a transitive
     importer that mentions a declaration A adds/removes/restates or a class whose instances A changes. Name-based and
     cheap (no Lean); a batch without such a link compiles nothing.
  2. For each link (A, B): B's delivered modules compiled with A's delivered modules (one call of
     tools/remote_compile_set.py through importer_compile._call: the existing single-file compile slots, lean -j1,
     LEAN_NUM_THREADS=1, 60 s per file); only when that FAILS, B's delivered modules alone (the published build: main
     without A). Results are kept by the hashes of both deliveries' texts (local/batch/pairs/<key>.json) and reused.
  3. B FAILS with A and compiles without A: A and B do not land together; the earlier of the two (the batch's order)
     lands. The later is B: B is returned to its group with the compiler message (it fails against main + A). The later
     is A: A waits; at the next batch B is on main and A's own related-modules recheck compiles B with A (and refuses
     A with the message if it still fails).
     Not decided (INFRA, SLOW, slots busy): the later one waits, at most SHEAF_BATCH_PAIR_WAIT s (3 h) from the first
     attempt; then it lands as before and the global build decides. When the earlier A lands and the later B waits, a
     record local/batch/pairs/pending/<B head>.json keeps A's delivered texts, so that the next batches still compile B
     with A (while A's texts are what main has); it is dropped once decided, A is no longer on main, or B's head moved.
     B fails without A too: not this check's verdict (the batch lands as before).
  The compiles run on SHEAF_BATCH_PAIR_PARALLEL (4) background threads of the lander; a batch waits for them at most
  SHEAF_BATCH_PAIR_TOTAL s (300), unfinished pairs count as not decided and go on compiling for the next step.

    tools/batch_pairs.py links <groupA>/<sha> <groupB>/<sha> ...     dry: the links between landed commits (each commit
                                                                     vs its first parent), no compile
"""
from __future__ import annotations
import hashlib, json, os, pathlib, sys, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import related_modules as rm  # noqa: E402

ROOT = rm.ROOT
DIR = pathlib.Path(ROOT) / "local" / "batch" / "pairs"
TOTAL = int(os.environ.get("SHEAF_BATCH_PAIR_TOTAL", "300"))
WAIT = float(os.environ.get("SHEAF_BATCH_PAIR_WAIT", "10800"))
PARALLEL = int(os.environ.get("SHEAF_BATCH_PAIR_PARALLEL", "4"))
BG_TOTAL = int(os.environ.get("SHEAF_BATCH_PAIR_CALL", "1800"))    # one pair's compiles, in the background
ROLES = ("item", "adapted", "new", "restored", "deleted")


def changes_of(D: dict) -> dict:
    """{module: (old, new)} of a read_delivery result (as related_modules.for_delivery)"""
    return {m["module"]: (m.get("old"), m.get("text")) for m in D["modules"]
            if m.get("role") in ROLES and m.get("old") != m.get("text")}


def texts_of(D: dict) -> dict:
    return {m["module"]: m.get("text") for m in D["modules"]}


def blob(text):
    if text is None:
        return None
    b = text.encode()
    return hashlib.sha1(b"blob %d\0" % len(b) + b).hexdigest()


def _hashes(texts: dict) -> dict:
    return {m: blob(t) for m, t in sorted(texts.items())}


def pair_key(a_texts: dict, b_texts: dict) -> str:
    return hashlib.sha1(json.dumps([_hashes(a_texts), _hashes(b_texts)], sort_keys=True).encode()).hexdigest()


def name(p: dict) -> str:
    return f"{p['group']}/{p['item']} {p['head'][:9]}"


# ---------------------------------------------------------------- 1. links

def links(parties: list[dict], graph: dict) -> list[dict]:
    """parties [{"texts": {module: text}, "changes": {module: (old, new)}, "landing": bool}] (texts delivered; a
    `landing` party may be B, a pending one only A); graph: the combined import graph (main + every party's texts).
    Returns [{"a": i, "b": j, "modules": [B's linked modules], "via": {module: why}}]."""
    owner = {}
    for j, p in enumerate(parties):
        if p.get("landing"):
            for m, t in p["texts"].items():
                if t is not None:
                    owner[m] = j
    out = []
    if not owner:
        return out
    for i, a in enumerate(parties):
        ch = a["changes"]
        if not ch or not any(j != i for j in set(owner.values())):
            continue
        mine = set(a["texts"])

        def text_of(m, mine=mine):        # only the batch's delivered texts are read: B is in the batch
            return None if m in mine or m not in owner else parties[owner[m]]["texts"].get(m)
        try:
            r = rm.related(ch, graph, text_of, cap=10 ** 6)
        except Exception:  # noqa: BLE001   a text the index cannot read: no link from it (the build decides)
            continue
        via = {}
        for u, mods in r["direct"].items():
            via[u] = "imports " + ", ".join(mods[:3])
        for x in r["transitive"]:
            via.setdefault(x["module"], "mentions " + ", ".join(x["mentions"][:4]))
        per = {}
        for u, why in via.items():
            j = owner.get(u)
            if j is not None and j != i:
                per.setdefault(j, {})[u] = why
        for j, v in sorted(per.items()):
            out.append({"a": i, "b": j, "modules": sorted(v), "via": v})
    return out


# ---------------------------------------------------------------- 2. compiles

def _ordered(texts: dict) -> list[tuple[str, str, bool]]:
    import importer_compile as ic
    return ic._ordered_own({"modules": [{"module": m, "text": t} for m, t in texts.items()]})


def _verdict(res: list[dict], mods: list[str], delivered: set) -> tuple[str, str]:
    """(OK|FAIL|INFRA|SLOW|NOT RUN, compiler output of the failures) over B's linked modules"""
    import importer_compile as ic
    st, out = {}, []
    for r in res or []:
        m = r["rel"][:-5].replace("/", ".")
        if m in mods:
            st[m] = ic.status_of(r, delivered)
            if st[m] == "FAIL":
                out.append(f"{m}:\n{(r.get('out') or '').strip()[-1500:]}")
    vals = [st.get(m, "NOT RUN") for m in mods]
    for v in ("FAIL", "NOT RUN", "INFRA", "SLOW"):
        if v in vals:
            return v, "\n".join(out)
    return "OK", ""


def compile_pair(a_texts: dict, b_texts: dict, mods: list[str], deadline: float, a_old: dict | None = None) -> dict:
    """{"with": status, "with_out": text, "without": status | None}: B's modules `mods` compiled with A's delivered
    texts, and (only after FAIL) without them: B's delivered texts with main's texts of the modules A changes (`a_old`,
    given explicitly: the published build may contain A already, e.g. a landing taken out again)."""
    import importer_compile as ic
    a_live = {m: t for m, t in a_texts.items() if t is not None}
    both = dict(a_live); both.update({m: t for m, t in b_texts.items() if t is not None})
    st, out = _verdict(ic._call(_ordered(both), ic.TOTAL, deadline), mods, set(both))
    r = {"with": st, "with_out": out[-3000:], "without": None}
    if st == "FAIL" and deadline - time.time() > ic.MIN_LEFT:
        b_live = {m: t for m, t in (a_old or {}).items() if t is not None and m not in b_texts}
        b_live.update({m: t for m, t in b_texts.items() if t is not None})
        r["without"], wo = _verdict(ic._call(_ordered(b_live), ic.TOTAL, deadline), mods, set(b_live))
        r["without_out"] = wo[-1500:]
    return r


def _read(p: pathlib.Path) -> dict | None:
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


def _write(p: pathlib.Path, d: dict) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + f".tmp{os.getpid()}")
    tmp.write_text(json.dumps(d, indent=1)); os.replace(tmp, p)


def decided(r: dict | None) -> bool:
    return bool(r) and (r.get("with") in ("OK",) or (r.get("with") == "FAIL" and r.get("without") in ("OK", "FAIL")))


# ---------------------------------------------------------------- 3. the batch

def _pending_parties(plans: list[dict], source) -> list[dict]:
    """the earlier deliveries a plan still has to be compiled with (records of earlier batches whose texts are on main)"""
    out = []
    live = {p["head"] for p in plans}
    for f in sorted((DIR / "pending").glob("*.json")) if (DIR / "pending").is_dir() else []:
        d = _read(f)
        if not d or d.get("b_head") not in live:
            if d and time.time() - d.get("time", 0) > 2 * WAIT:
                f.unlink(missing_ok=True)       # B moved on (a new head, returned, landed): forget the record
            continue
        if any(source(m) != t for m, t in d["a_texts"].items()):
            f.unlink(missing_ok=True)           # A is not (or no longer) what main has: nothing to compile against
            continue
        out.append({"texts": d["a_texts"], "changes": {m: tuple(v) for m, v in d["a_changes"].items()},
                    "landing": False, "name": d["a_name"], "for": d["b_head"], "first": d.get("first")})
    return out


_BG = {"lock": threading.Lock(), "queue": [], "busy": set(), "workers": 0}


def _busy(keys) -> bool:
    with _BG["lock"]:
        return any(k in _BG["busy"] for k in keys)


def _submit(jobs, compile) -> list[str]:
    """queue the pair compiles on the lander's background pool (PARALLEL threads; a key queued or compiling is not queued
    again); they write DIR/<key>.json. Returns the keys."""
    with _BG["lock"]:
        for k, a, b, x in jobs:
            if k not in _BG["busy"]:
                _BG["busy"].add(k); _BG["queue"].append((k, a, b, x, compile))
        start = max(0, min(PARALLEL, len(_BG["queue"])) - _BG["workers"])
        _BG["workers"] += start
    for _ in range(start):
        threading.Thread(target=_bg_worker, daemon=True).start()
    return [j[0] for j in jobs]


def _bg_worker() -> None:
    while True:
        with _BG["lock"]:
            if not _BG["queue"]:
                _BG["workers"] -= 1
                return
            k, a, b, x, compile = _BG["queue"].pop(0)
        try:
            try:
                r = compile(a["texts"], b["texts"], x["modules"], time.time() + BG_TOTAL,
                            a_old={m: v[0] for m, v in a["changes"].items()})
            except Exception as e:  # noqa: BLE001
                r = {"with": "INFRA", "with_out": repr(e)[:300], "without": None}
            old = _read(DIR / f"{k}.json") or {}
            _write(DIR / f"{k}.json", dict(r, first=old.get("first") or time.time(), a=a["name"], b=b["name"],
                                          modules=x["modules"], via=x["via"], time=time.strftime("%FT%T%z")))
        except Exception:  # noqa: BLE001   a result that cannot be written is compiled again next time
            pass
        finally:
            with _BG["lock"]:
                _BG["busy"].discard(k)


def split(plans: list[dict], graph: dict, log, compile=compile_pair, source=None, now=time.time) -> tuple:
    """plans: checked stage-3 plans in landing order; graph: the import graph with every plan's texts in place.
    Returns (plans that land, [(plan, why)] that wait, [(plan, why)] returned to their groups)."""
    if source is None:
        import importer_compile as ic
        source = ic.source
    parties = [{"texts": texts_of(p["D"]), "changes": changes_of(p["D"]), "landing": True, "name": name(p), "plan": p}
               for p in plans]
    pend = _pending_parties(plans, source)
    parties += pend
    g = graph
    if pend:
        g = dict(graph)
        for p in pend:
            g.update({m: set(rm.li.imports_of(t)) for m, t in p["texts"].items() if t is not None})
    L = links(parties, g)
    # a pending A belongs only to the plan it was recorded for
    L = [x for x in L if parties[x["a"]].get("landing") or parties[x["a"]].get("for") == parties[x["b"]]["plan"]["head"]]
    if not L:
        return plans, [], []
    t0 = now()
    for f in DIR.glob("*.json"):              # results of pairs not seen for a long time
        try:
            if time.time() - f.stat().st_mtime > 2 * WAIT:
                f.unlink(missing_ok=True)
        except OSError:
            pass
    res, todo = {}, []
    for x in L:
        a, b = parties[x["a"]], parties[x["b"]]
        k = pair_key(a["texts"], b["texts"])
        x["key"] = k
        r = _read(DIR / f"{k}.json")
        if decided(r):
            res[k] = r
        else:
            res[k] = dict(r or {}, first=(r or {}).get("first") or a.get("first") or t0)
            if r is None:
                _write(DIR / f"{k}.json", res[k])       # the wait cap counts from the first attempt
            todo.append(x)
    if todo:
        log(f"batch pairs: {len(L)} linked pair(s) in the batch, {len(todo)} to compile: "
            + "; ".join(f"{parties[x['b']]['name']} with {parties[x['a']]['name']} ({', '.join(x['modules'][:2])})"
                        for x in todo[:6]))
        keys = _submit([(x["key"], parties[x["a"]], parties[x["b"]], x) for x in todo], compile)
        # the batch waits for them at most TOTAL s; the rest go on in the background (results kept for the next step)
        t_end = time.time() + TOTAL
        while time.time() < t_end and _busy(keys):
            time.sleep(0.5)
        for x in todo:
            r = _read(DIR / f"{x['key']}.json")
            if r:
                res[x["key"]] = dict(r, first=res[x["key"]]["first"])

    out_wait, out_ret, record = {}, {}, set()
    for x in L:
        a, b, r = parties[x["a"]], parties[x["b"]], res[x["key"]]
        ia = x["a"] if a.get("landing") else -1          # a pending A landed in an earlier batch: earlier
        later = x["b"] if ia < x["b"] else x["a"]
        if r.get("with") == "OK" or (r.get("with") == "FAIL" and r.get("without") == "FAIL"):
            continue
        if r.get("with") == "FAIL" and r.get("without") == "OK":
            if later == x["b"]:
                out_ret.setdefault(later, (
                    f"batch pair check (tools/batch_pairs.py): {', '.join(x['modules'])} as delivered fails to compile "
                    f"against the delivery {a['name']} ({'landed before' if ia < 0 else 'landing first in the same batch'}; "
                    f"{', '.join(x['via'][m] for m in x['modules'][:2])}), and compiles without it. "
                    f"Adapt the delivery to {a['name']}'s texts (they are on {'main' if ia < 0 else 'main once it lands'}), "
                    f"compile, deliver again.\n{r.get('with_out', '')[-2400:]}", a))
            else:
                out_wait.setdefault(later, f"batch pair check: the earlier delivery {b['name']} of this batch fails "
                                    f"against this one ({', '.join(x['modules'][:2])}); it lands first, this one waits "
                                    f"(its related-modules recheck then compiles it with that module)")
            continue
        # not decided yet
        if now() - (r.get("first") or t0) < WAIT:
            out_wait.setdefault(later, f"batch pair check not finished: {b['name']} ({', '.join(x['modules'][:2])}) "
                                f"with {a['name']}: {r.get('with') or 'not compiled yet'}"
                                + (f" / without {r['without']}" if r.get("without") else ""))
            if later == x["b"]:
                record.add((x["key"], x["a"], x["b"]))
        # over the cap: lands as before, the global build decides
    for j in out_ret:
        out_wait.pop(j, None)
    land = [p for j, p in enumerate(parties) if p.get("landing") and j not in out_wait and j not in out_ret]
    # pending records: the later B waits while its earlier A lands (or is on main already)
    landing_heads = {p["plan"]["head"] for p in land}
    for key, ia, jb in record:
        a, b = parties[ia], parties[jb]
        if jb in out_ret or (a.get("landing") and a["plan"]["head"] not in landing_heads):
            continue
        _write(DIR / "pending" / f"{b['plan']['head']}.json",
               {"b_head": b["plan"]["head"], "b_name": b["name"], "a_name": a["name"], "a_texts": a["texts"],
                "a_changes": {m: list(v) for m, v in a["changes"].items()}, "first": res[key].get("first"),
                "time": now()})
    for j, (_why, a) in out_ret.items():
        (DIR / "pending" / f"{parties[j]['plan']['head']}.json").unlink(missing_ok=True)
    # a decided pending pair: its record is done
    for x in L:
        a = parties[x["a"]]
        if not a.get("landing") and x["b"] not in out_wait:
            (DIR / "pending" / f"{parties[x['b']]['plan']['head']}.json").unlink(missing_ok=True)
    waits = [(parties[j]["plan"], w) for j, w in sorted(out_wait.items())]
    rets = [(parties[j]["plan"], w) for j, (w, _a) in sorted(out_ret.items())]
    return [p["plan"] for p in land], waits, rets


# ---------------------------------------------------------------- dry run on landed commits

def main(argv: list[str]) -> int:
    if len(argv) < 3 or argv[0] != "links":
        print(__doc__); return 2
    import subprocess
    plans = []
    for spec in argv[1:]:
        grp, sha = spec.split("/", 1)
        files = subprocess.run(["git", "diff", "--name-only", f"{sha}^", sha, "--", "lean"], cwd=ROOT,
                               capture_output=True, text=True, check=True).stdout.split()
        mods = []
        for p in files:
            if not p.endswith(".lean") or "/.sandbox/" in p:
                continue
            m = p[len("lean/"):-len(".lean")].replace("/", ".")
            show = lambda rev: (lambda r: r.stdout if r.returncode == 0 else None)(
                subprocess.run(["git", "show", f"{rev}:{p}"], cwd=ROOT, capture_output=True, text=True))
            old, new = show(f"{sha}^"), show(sha)
            mods.append({"module": m, "old": old, "text": new, "role": "item" if old is not None else "new"})
        plans.append({"group": grp, "item": mods[0]["module"] if mods else "?", "head": sha, "D": {"modules": mods}})
    import import_cycles as cy
    g = cy.graph(rm.li.LEAN)
    for p in plans:
        g = cy.overlay(g, texts_of(p["D"]))
    parties = [{"texts": texts_of(p["D"]), "changes": changes_of(p["D"]), "landing": True, "name": name(p)} for p in plans]
    for x in links(parties, g):
        print(f"{parties[x['b']]['name']} depends on {parties[x['a']]['name']}: "
              + "; ".join(f"{m} ({w})" for m, w in x["via"].items()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
