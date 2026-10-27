#!/usr/bin/env python3
"""Compile the direct importers of the modules a stage-3 delivery changes, against the delivered versions (decision of
the human, 2026-10-26: a stage-3 delivery that changes other files is read, and the reader checks that the change keeps
every module the delivery did not touch compiling). The tool informs, the reader decides; at landing the same compile
is repeated for the importers that changed since (recheck, below), and that one may refuse.

    tools/importer_compile.py <group> <item> [--head <sha>] [--cap N]     prints the evidence (Markdown)
    tools/importer_compile.py recheck <group> <item> [--head <sha>]       the landing's recheck, dry (prints, refuses nothing)

Which importers: for each existing module the delivery changes (the item and every adapted module) whose interface
changes (leanindex.interface_changes: a statement, a definition, an instance or attribute, an import, a removed
declaration, variable/open/notation, an added declaration), its direct importers that the delivery does not change. A proof-only change
cannot break an importer; its importers are listed, not compiled. 2026-10-27 (the human): ALL of them are compiled (the
cap of 12 let X7's SfP1ChartExchange through: 48 direct importers, 12 compiled, 4445 modules quarantined).

How: one call of tools/remote_compile_set.py (the service the workers' lcompile uses) per chunk, each holding one of the
project's single-file compile slots (local/compile-slots, FIFO tickets): first one call with the delivered modules alone
(they go into the shared result cache, rset-cache), then the importers split over at most SHEAF_S3_IMPORTER_PARALLEL (8)
calls at once, each importer alone against the delivered modules, `lean -j1`, LEAN_NUM_THREADS=1, the 60 s acceptance
limit of one file. The importers' sources are the working tree's (the candidate: main plus the open landings). Only
direct importers are compiled: a transitive importer is verified by the global build. The whole step has
SHEAF_S3_IMPORTER_TOTAL (720) seconds; what did not finish is named NOT RUN.

Result per importer: OK, FAIL (a compiler error), SLOW (over 60 s), INFRA (not a verdict on the delivery: a module the
importer needs has no .olean in the published build, a dependency failed in the private overlay, a stale published
module that already contains a declaration, no compile slot; retried once), NOT RUN (the time ran out).

Evidence: local/importer-checks/<head>.json (version 2) keeps per importer its status, compiler output and the git blob
hash (`git hash-object`) of the source compiled, and whether that source had a `sorry` (a sorry stub compiles vacuously).
A second packet of the same head reuses a result only when the importer's source is unchanged.

Recheck at landing (tools/batch_land.py _check -> importer_recheck, a reader-passed stage-3 delivery only): every
direct importer whose source hash differs from the evidence, that is not in it, or whose evidence is not OK, is
compiled again against the texts that will land. An importer that FAILS with the delivery and compiles on main without
it refuses the landing (the delivery goes back to its writer with the compiler message); one that fails on main too is
pre-existing, and INFRA/SLOW/NOT RUN do not refuse. Record: local/importer-checks/<head>.recheck.json.
"""
from __future__ import annotations
import hashlib, io, json, math, os, pathlib, re, signal, subprocess, sys, tarfile, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import stage2_delivery as s2  # noqa: E402
import stage3_delivery as s3  # noqa: E402

ROOT = s3.ROOT
LEAN = pathlib.Path(ROOT) / "lean"
# CAP, CHUNK, BUDGET, _call are also used by tools/merge_jobs.py (its own importer compile, maintained there): unchanged
CAP = int(os.environ.get("SHEAF_S3_IMPORTER_CAP", "12"))
CHUNK = 4
PARALLEL = int(os.environ.get("SHEAF_S3_IMPORTER_PARALLEL", "8"))
BUDGET = int(os.environ.get("SHEAF_S3_IMPORTER_BUDGET", "480"))
TOTAL = int(os.environ.get("SHEAF_S3_IMPORTER_TOTAL", "720"))       # the packet's step (prep_s3 waits 900 s for the packet)
RECHECK_TOTAL = int(os.environ.get("SHEAF_S3_RECHECK_TOTAL", "600"))
RECHECK_PARALLEL = int(os.environ.get("SHEAF_S3_RECHECK_PARALLEL", "4"))
ICHUNK = max(1, int(os.environ.get("SHEAF_S3_IMPORTER_CHUNK", "2")))   # importers per compile call (with the delivered modules)
MIN_LEFT = 60                    # no new compile call is started with less time left than this before the deadline
NOCAP = 10 ** 9
CACHE = pathlib.Path(ROOT) / "local" / "importer-checks"
RSET = pathlib.Path(__file__).resolve().parent / "remote_compile_set.py"


def rel_of(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def upstream(rel: str) -> bool:
    return rel.startswith("WeilConjectures/") or rel.startswith("Comparator/")


def blob_hash(text: str | None) -> str | None:
    """git hash-object of the text."""
    if text is None:
        return None
    b = text.encode()
    return hashlib.sha1(b"blob %d\0" % len(b) + b).hexdigest()


_SORRY = re.compile(r"(?<![\w.'])sorry(?![\w'])")
_COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)


def has_sorry(text: str | None) -> bool:
    return bool(text) and bool(_SORRY.search(_COMMENT.sub(" ", text)))


def source(mod: str) -> str | None:
    try:
        return (LEAN / rel_of(mod)).read_text()
    except OSError:
        return None


def interface_changed(m: dict) -> bool:
    d = m["diff"]
    # 2026-10-27: an added declaration too (it can clash with one of the same name an importer declares or imports)
    return bool(d.get("interface") or d.get("statement_changed") or d.get("removed") or d.get("public_imports_changed")
                or d.get("removed_imports") or d.get("added"))


def plan(D: dict, cap: int = NOCAP) -> dict:
    """{changed: [(module, role, interface?)], compile: [importer], skipped: [importer], proof_only: {module: [importers]}}"""
    delivered = {m["module"] for m in D["modules"]}
    users = D.get("users") or {}
    changed, cand, proof_only = [], {}, {}
    for m in D["modules"]:
        if m["role"] not in ("item", "adapted") or m.get("old") is None or m.get("text") is None:
            continue
        imp = [u for u in s3.importers(m["module"]) if u not in delivered]
        itf = interface_changed(m)
        changed.append((m["module"], m["role"], itf, len(imp)))
        if not itf:
            proof_only[m["module"]] = imp
            continue
        for u in imp:
            cand.setdefault(u, []).append(m["module"])
    order = sorted(cand, key=lambda u: (u not in users, u))
    return {"changed": changed, "compile": order[:cap], "skipped": order[cap:], "via": cand, "proof_only": proof_only}


def _call(jobs_src: list[tuple[str, str, bool]], timeout: int, deadline: float) -> list[dict]:
    """One remote_compile_set call: jobs (rel, text, out). Returns its results ([{rel, rc, out, secs}])."""
    buf = io.BytesIO()
    man = {"timeout": 60, "stop_on_fail": False, "jobs": []}
    with tarfile.open(fileobj=buf, mode="w:gz", compresslevel=3) as t:
        for rel, text, out in jobs_src:
            b = text.encode()
            ti = tarfile.TarInfo("lean/" + rel); ti.size = len(b); ti.mtime = int(time.time())
            t.addfile(ti, io.BytesIO(b))
            man["jobs"].append({"rel": rel, "upstream": upstream(rel), "out": bool(out), "probe": ""})
        mb = json.dumps(man).encode(); ti = tarfile.TarInfo("manifest.json"); ti.size = len(mb)
        t.addfile(ti, io.BytesIO(mb))
    left = max(30, int(deadline - time.time()))
    p = subprocess.Popen([sys.executable, str(RSET)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, cwd=str(ROOT), start_new_session=True)
    try:
        so, se = p.communicate(buf.getvalue(), timeout=min(timeout, left))
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGTERM)   # the call's own session: rset.py and its Lean children only
        except OSError:
            pass
        p.wait(timeout=30)
        return [{"rel": r, "rc": None, "budget": True, "out": "not compiled: the step's time ran out (waiting for a "
                                                  "compile slot or compiling)", "secs": 0} for r, _t, _o in jobs_src]
    if p.returncode != 0 or not so:
        why = {75: "no compile slot within the service's wait, or no published build"}.get(p.returncode, f"exit {p.returncode}")
        return [{"rel": r, "rc": None, "out": f"not compiled: the compile service answered {why}: {se.decode(errors='replace')[-300:]}",
                 "secs": 0} for r, _t, _o in jobs_src]
    with tarfile.open(fileobj=io.BytesIO(so), mode="r:gz") as t:
        res = json.load(t.extractfile("result.json"))["results"]
    return res


def failing_last_build() -> set:
    try:
        d = json.loads((pathlib.Path(ROOT) / "local" / "builds" / "last.json").read_text())
        f = d.get("failing") or []
        return set(f if isinstance(f, list) else []) if d.get("result") == "red" else set()
    except (OSError, ValueError):
        return set()


_MISSING = re.compile(r"object file .* of module (\S+) does not exist")
_ALREADY = re.compile(r"environment already contains '[^']*' from (\S+)")


def status_of(r: dict, delivered: set) -> str:
    """OK / FAIL / SLOW / INFRA / NOT RUN of one compile result."""
    rc, out = r.get("rc"), r.get("out") or ""
    if rc == 0:
        return "OK"
    if rc is None:
        return "NOT RUN" if r.get("budget") else "INFRA"
    if "Dependency source unavailable" in out or "failed in the private compile overlay" in out:
        return "INFRA"
    m = _MISSING.search(out)
    if m and m.group(1) not in delivered:
        return "INFRA"
    m = _ALREADY.search(out)
    if m and m.group(1).rstrip(".,;:") not in delivered:
        return "INFRA"     # a published module built against the old version of a delivered one (stale for this compile)
    if rc == 124:
        return "SLOW"
    return "FAIL"


def _ordered_own(D: dict) -> list[tuple[str, str, bool]]:
    """The delivered modules in their import order (a sibling first), each compiled into the call's .lbuild."""
    delivered = [m for m in D["modules"] if m.get("text") is not None]
    names = {m["module"] for m in delivered}
    done, ordered = set(), []
    while len(ordered) < len(delivered):
        step = [m for m in delivered if m["module"] not in done
                and all(i in done or i not in names for i in s2.imports(m["text"]))]
        if not step:
            step = [m for m in delivered if m["module"] not in done]
        for m in step:
            done.add(m["module"]); ordered.append(m)
    return [(rel_of(m["module"]), m["text"], True) for m in ordered]


def compile_importers(D: dict | None, mods: list[str], deadline: float, parallel: int = PARALLEL,
                      retry_infra: bool = True, chunk: int = ICHUNK, on_result=None) -> dict:
    """{importer: {rc, out, secs, status, hash, sorry}} and "__own__": [failures of the delivered modules].
    D None: each importer alone against the published build (main, without the delivery). on_result(importer, result)
    is called as soon as an importer has its final result of this call (not for NOT RUN), so that a caller can keep it."""
    own = _ordered_own(D) if D else []
    delivered = {r[:-5].replace("/", ".") for r, _t, _o in own}
    results: dict = {}
    texts = {}
    for u in mods:
        t = source(u)
        if t is None:
            results[u] = {"rc": None, "out": "not compiled: no source in lean/", "secs": 0, "status": "INFRA", "hash": None,
                          "sorry": False}
        else:
            texts[u] = t
    todo = [u for u in mods if u in texts]
    if not todo:
        return results
    if own:
        # the delivered modules alone first: their compiled files go into the shared cache, so the parallel calls
        # below take them from it instead of compiling them again (or waiting on its per-key lock with a slot held)
        for r in _call(own, TOTAL, deadline):
            if r.get("rc") not in (0, None):
                results.setdefault("__own__", []).append({"module": r["rel"][:-5].replace("/", "."), "rc": r["rc"],
                                                          "out": (r.get("out") or "")[-1500:]})

    lock = threading.Lock()

    def report(mods):
        if on_result:
            with lock:
                for u in mods:
                    if u in results:
                        on_result(u, results[u])

    def run_round(batch, final):
        # 2026-10-27: small chunks (SHEAF_S3_IMPORTER_CHUNK importers per call) taken by `parallel` threads until the
        # deadline. One call per parallel slice of ~12 importers never finished within the step's time, and a call cut
        # at the deadline returns nothing, so every recheck started from zero (deliveries waited 3 h for nothing).
        chunks = [batch[k:k + chunk] for k in range(0, len(batch), chunk)]

        def work():
            while True:
                with lock:
                    if not chunks or deadline - time.time() < MIN_LEFT:
                        return
                    c = chunks.pop(0)
                res = _call(list(own) + [(rel_of(u), texts[u], False) for u in c], TOTAL, deadline)
                got = []
                with lock:
                    for r in res or []:
                        mod = r["rel"][:-5].replace("/", ".")
                        if mod in delivered or mod not in texts:
                            continue
                        results[mod] = {"rc": r.get("rc"), "out": (r.get("out") or "")[-2500:], "secs": r.get("secs"),
                                        "status": status_of(r, delivered), "hash": blob_hash(texts[mod]),
                                        "sorry": has_sorry(texts[mod])}
                        got.append(mod)
                # an INFRA result is retried once below: reported only after its retry (or at the end)
                report([u for u in got if final or results[u]["status"] not in ("INFRA", "NOT RUN")])
        # threads, not concurrent.futures: tools/queue.py shadows the standard queue module that it imports
        ths = [threading.Thread(target=work) for _ in range(max(1, min(parallel, len(chunks))))]
        for th in ths: th.start()
        for th in ths: th.join()
    run_round(todo, final=not retry_infra)
    if retry_infra:
        again = [u for u in todo if (results.get(u) or {}).get("status") == "INFRA"]
        if again and deadline - time.time() > 90:
            first = {u: results[u] for u in again}
            run_round(again, final=False)
            for u in again:
                results[u]["retried"] = True
                if results[u]["status"] == "NOT RUN":
                    results[u] = dict(first[u], retried=True)
        report(again)
    for u in todo:
        results.setdefault(u, {"rc": None, "out": "no result", "secs": 0, "status": "NOT RUN",
                               "hash": blob_hash(texts[u]), "sorry": has_sorry(texts[u])})
    return results


def own_hashes(D: dict) -> dict:
    return {m["module"]: blob_hash(m.get("text")) for m in D["modules"]}


def load_evidence(head: str) -> dict | None:
    try:
        return json.loads((CACHE / f"{head}.json").read_text())
    except (OSError, ValueError):
        return None


def _save(path: pathlib.Path, d: dict) -> None:
    try:
        CACHE.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(f".tmp{os.getpid()}")
        tmp.write_text(json.dumps(d))
        os.replace(tmp, path)
    except OSError:
        pass


def evidence(D: dict, item: str, head: str, cap: int = NOCAP) -> str:
    """The evidence section for the review packet (Markdown)."""
    P = plan(D, cap)
    old = load_evidence(head) or {}
    oldres = old.get("results") or {} if old.get("version") == 2 else {}
    t0 = time.time()
    results, todo = {}, []
    for u in P["compile"]:
        r = oldres.get(u)
        if r and r.get("status") in ("OK", "FAIL", "SLOW") and r.get("hash") and r["hash"] == blob_hash(source(u)):
            results[u] = r                       # same importer source, same head: the earlier result stands
        else:
            todo.append(u)
    if todo:
        results.update(compile_importers(D, todo, t0 + TOTAL))
    elif oldres.get("__own__"):
        results["__own__"] = oldres["__own__"]
    _save(CACHE / f"{head}.json", {"version": 2, "head": head, "item": item, "time": time.strftime("%FT%T%z"),
                                   "own": own_hashes(D), "compile": P["compile"], "results": results,
                                   "seconds": round(time.time() - t0)})
    red = failing_last_build()
    o = []; w = o.append
    w("## 3b. Downstream compatibility: the direct importers compiled against this delivery (tools/importer_compile.py)\n")
    w("The rule (the human, 2026-10-26): this delivery changes other files, so it is read; besides the usual semantic "
      "checks, it must keep every module and node it did not touch compiling. The compile below is evidence, not a "
      "verdict: an importer that fails (`FAIL`) or exceeds 60 s (`SLOW`) because of this delivery is a RETURN reason "
      "you cite (or FIX, when you can repair it inside the delivery's own files without touching the importer). "
      "`INFRA` is not about the delivery (a module the importer needs has no compiled file, retried once). It shows the "
      "importers as they are NOW: one marked `sorry stub` compiles vacuously, and the lander compiles again every "
      "importer that changes before the landing.\n")
    for mod, role, itf, n in P["changed"]:
        w(f"- {mod} ({role}): " + ("interface changed" if itf else "proof-only change") + f"; {n} direct importer(s) "
          "outside the delivery")
    for mod, imp in P["proof_only"].items():
        if imp:
            w(f"- importers of {mod} not compiled (a proof-only change cannot break them): {', '.join(imp[:20])}"
              + (f" (+{len(imp) - 20})" if len(imp) > 20 else ""))
    own_bad = results.get("__own__")
    if own_bad:
        for x in own_bad:
            w(f"- the delivered module {x['module']} itself did not compile here (exit {x['rc']}): the importers' results "
              f"below are not meaningful.\n```\n{x['out']}\n```")
    if not P["compile"]:
        w("\nNo importer to compile (none outside the delivery, or no interface change).\n")
    else:
        counts = {}
        for u in P["compile"]:
            st = (results.get(u) or {}).get("status", "NOT RUN")
            counts[st] = counts.get(st, 0) + 1
        w(f"\nCompiled: {len(P['compile'])} importer(s): " + ", ".join(f"{v} {k}" for k, v in sorted(counts.items()))
          + (f"; NOT compiled (cap {cap}): {', '.join(P['skipped'])}" if P["skipped"] else "") + "\n")
        for u in P["compile"]:
            r = results.get(u) or {"rc": None, "out": "no result", "status": "NOT RUN"}
            st = r.get("status", "NOT RUN")
            pre = " (it is also failing in the last global build: pre-existing, judge only what this delivery changes)" \
                if u in red and st != "OK" else ""
            w(f"### {u}: {st}{pre} (uses {', '.join(P['via'].get(u, []))}"
              + (f"; mentions {', '.join((D.get('users') or {}).get(u, [])[:6])}" if (D.get("users") or {}).get(u) else "")
              + ("; sorry stub: compiles vacuously, its statements' users are what matters" if r.get("sorry") else "")
              + (f"; {r.get('secs')} s" if r.get("secs") else "") + (f"; source {r['hash'][:10]}" if r.get("hash") else "") + ")")
            if st != "OK":
                w("```\n" + (r.get("out") or "").strip()[-2500:] + "\n```")
    return "\n".join(o) + "\n"


def recheck(D: dict, head: str, total: int = RECHECK_TOTAL, write: bool = True) -> dict:
    """The landing's recheck. Returns {"compiled": {mod: why}, "new_fail": {mod: out}, "pre_existing": [...],
    "other": {mod: status}, "not_run": [...], "first": t, "seconds": n}; refusing or waiting is the caller's
    (tools/batch_land.py importer_recheck). Incremental: the results of earlier rechecks of the same head and delivered
    texts are kept in local/importer-checks/<head>.recheck.json and reused for an importer whose source is unchanged, so
    a recheck cut short by busy compile slots goes on where it stopped."""
    t0 = time.time(); deadline = t0 + total
    P = plan(D)
    ev = load_evidence(head) or {}
    evres = (ev.get("results") or {}) if ev.get("version") == 2 else {}
    own = own_hashes(D)
    rf = CACHE / f"{head}.recheck.json"
    try:
        prev = json.loads(rf.read_text())
        if prev.get("own") != own:
            prev = {}
    except (OSError, ValueError):
        prev = {}
    done = prev.get("results") or {}
    why = {}
    moved = [m for m, h in own.items() if evres and (ev.get("own") or {}).get(m, h) != h]
    for u in P["compile"]:
        r = evres.get(u)
        cur = blob_hash(source(u))
        if moved:
            why[u] = "the delivered text of " + ", ".join(moved[:3]) + " differs from the one reviewed (a reviewer's fix or a merge)"
        elif r is None:
            why[u] = "not in the review's evidence" if ev else "no review evidence for this head"
        elif r.get("hash") != cur:
            why[u] = "source changed since the review" + (" (was a sorry stub)" if r.get("sorry") else "")
        elif r.get("status") != "OK":
            why[u] = f"{r.get('status')} at review"
    out = {"head": head, "time": time.strftime("%FT%T%z"), "first": prev.get("first") or t0, "own": own,
           "compiled": why, "new_fail": {}, "pre_existing": [], "other": {}, "not_run": [], "own_failed": None,
           "results": {}}
    todo = []
    for u in why:
        d0 = done.get(u)
        if d0 and d0.get("hash") == blob_hash(source(u)) and d0.get("verdict") in ("OK", "PRE", "SLOW", "INFRA", "UNCONFIRMED"):
            out["results"][u] = d0
        else:
            todo.append(u)
    def keep(u, r):
        # a result is written to the recheck record as it arrives (the same entry as below), so an attempt cut by the
        # deadline or stopped still leaves its finished importers to the next one; a FAIL is decided below (main compile)
        st = r.get("status")
        if st in ("OK", "SLOW", "INFRA") and u in why:
            out["results"][u] = {"hash": r.get("hash"), "status": st, "verdict": st}
            if write:
                _save(rf, out)
    if todo:
        res = compile_importers(D, sorted(todo), deadline, parallel=RECHECK_PARALLEL, on_result=keep)
        out["own_failed"] = res.get("__own__")
        bad = []
        for u in todo:
            r = res.get(u) or {}
            st = r.get("status", "NOT RUN")
            if st == "FAIL":
                bad.append(u)
            elif st != "NOT RUN":
                out["results"][u] = {"hash": r.get("hash"), "status": st, "verdict": st if st in ("OK", "SLOW", "INFRA") else st}
        if bad and out["own_failed"]:
            for u in bad:
                out["results"][u] = {"hash": res[u].get("hash"), "status": "FAIL", "verdict": "UNCONFIRMED",
                                     "note": "a delivered module itself did not compile here"}
        elif bad:
            main = compile_importers(None, bad, max(deadline, time.time() + 300), parallel=RECHECK_PARALLEL)
            red = failing_last_build()
            for u in bad:
                ms = (main.get(u) or {}).get("status")
                h = res[u].get("hash")
                if ms == "OK":
                    out["new_fail"][u] = res[u].get("out") or ""
                    out["results"][u] = {"hash": h, "status": "FAIL", "verdict": "NEW_FAIL"}
                elif ms in ("FAIL", "SLOW") or u in red:
                    out["results"][u] = {"hash": h, "status": "FAIL", "verdict": "PRE"}
                elif ms == "NOT RUN":
                    pass                                  # decided by a later recheck
                else:
                    out["results"][u] = {"hash": h, "status": "FAIL", "verdict": "UNCONFIRMED", "note": f"main {ms}"}
    for u in why:
        v = (out["results"].get(u) or {}).get("verdict")
        if v is None:
            out["not_run"].append(u)
        elif v == "PRE":
            out["pre_existing"].append(u)
        elif v not in ("OK", "NEW_FAIL"):
            out["other"][u] = v
    out["seconds"] = round(time.time() - t0)
    if write:
        _save(rf, out)
    return out


def main(argv: list[str]) -> int:
    rck = bool(argv) and argv[0] == "recheck"
    if rck:
        argv = argv[1:]
    args = [a for k, a in enumerate(argv) if not a.startswith("--") and not (k and argv[k - 1] in ("--head", "--cap"))]
    if len(args) != 2:
        print(__doc__); return 2
    g, item = args
    head = argv[argv.index("--head") + 1] if "--head" in argv else None
    cap = int(argv[argv.index("--cap") + 1]) if "--cap" in argv else NOCAP
    G = s2.Git(ROOT)
    ref = head or f"deliver/{g}/{item}"
    sha = G.run("rev-parse", ref).strip()
    base = G.run("merge-base", "sheaf-dag", sha).strip()
    D = s3.read_delivery(G, sha, base, g, item)
    if rck:
        print(json.dumps(recheck(D, sha, write=False), indent=1)[:20000])
        return 0
    print(evidence(D, item, sha, cap))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
