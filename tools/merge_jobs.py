#!/usr/bin/env python3
"""Merge jobs: a delivery whose file changed since its base is merged by a merge agent, not by a text merge (the human,
2026-10-26: landings whose file another landing of the same day touched reverted at 14.9 % against 2.0 % alone, ~58 %
of all reverts; `git merge-file` joined the characters, not the intents).

A conflict is found as soon as a delivery waits to land (tools/batch_land.py: its checks run in the lander's pool while
the open batch is built):
  main      a file the delivery changes changed on sheaf-dag since the delivery's base (another landing wrote it); found
            by check() itself, which then makes the delivery wait (no refusal, no landing) until the job is done;
  pending   two checked deliveries waiting to land write the same file; the one the batch takes first (A) lands as it
            is, the other (B) gets a job now that merges it onto A's text, so B lands the moment A has landed.
Each conflict is one job local/merge-jobs/<G>__<item>/job.json (one per delivery; generation `gen`; the texts under
g<gen>/{base,target,ours,other}/lean/...): base = the common version, target = main's text now (or A's text), ours = the
delivery's text. A merge agent (lane M of the cc review service, ~/weil-review-svc/mergelane.py) writes a merge that
keeps both intents; `finish` here compiles the merged files with the delivery's other modules and, when the interface
changed, their direct importers, each alone (tools/remote_compile_set.py: lean -j1, LEAN_NUM_THREADS=1, 60 s). Green:
state `merged`, and check() lands the merged text in place of the delivery's text, as long as main's file is still the
target. Not mergeable (or still red after the second attempt): state `failed`, and check() refuses the delivery: it goes
back to its group with the agent's explanation (tools/batch_land.py give_back). A job whose target moved (main changed
again) is requested again on the new main (`refresh`, the runner calls it before and during every session).

Widened 2026-10-26 evening (the human): the agent may change ANY file of the delivery (its other Lean modules and its
node files), not only the conflicting one; every file it changes is compiled with its direct importers. DAG node
conflicts are merge jobs too: a node the delivery creates that exists on main now (another landing created it), or a
node field (lean, proof, proof_deps, proof_origin, statement, stmt_deps, statement_change, tool_uses) both the delivery
and main changed differently since the base. The merged node lands as a change of main's node and must pass the
delivery checks of tools/stage3_delivery.py (check_nodes: fields a stage-3 delivery may set, dependencies that exist,
no new cycle, statement-change rules, new-node rules) and its `lean` record must match the merged Lean.

Usage (SHEAF_LEAD=L-only):
  tools/merge_jobs.py scan                  dry run: the conflicts of the delivery branches now (writes nothing)
  tools/merge_jobs.py status [--json]       the jobs by state (queue report)
  tools/merge_jobs.py refresh <key>         re-request a main job whose target file changed on main since
  tools/merge_jobs.py start <key> <gen> <run-dir> <pid>
  tools/merge_jobs.py finish <key> <gen> <run-dir> MERGED|CANNOT <explanation-file>
  tools/merge_jobs.py retry <key> <gen> <why>   (a session that ended without an answer: requested again, after a pause)
  tools/merge_jobs.py gc                    remove jobs whose delivery head is gone (landed, returned, moved) for 2 h
"""
from __future__ import annotations
import contextlib, fcntl, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

TOOLS = pathlib.Path(os.environ.get("MERGE_JOBS_TOOLS") or pathlib.Path(__file__).resolve().parent)   # override: a test copy
ROOT = TOOLS.parent
JOBS = pathlib.Path(os.environ.get("MERGE_JOBS_DIR") or ROOT / "local" / "merge-jobs")   # override: a dry run
MAIN = "sheaf-dag"
ATTEMPTS = 2              # agent answers that do not compile: a second session gets the compiler's message
MAX_SESSIONS = 4          # sessions that end without an answer (not counting token limits) before the job fails
RETRY_PAUSE = 300         # seconds before a session that ended without an answer is tried again


def now() -> str:
    return time.strftime("%FT%TZ", time.gmtime())


def sha(t):
    return None if t is None else hashlib.sha256(t.encode()).hexdigest()


def key(g: str, item: str) -> str:
    return f"{g}__{item}"


def jdir(k: str) -> pathlib.Path:
    return JOBS / k


def read(k: str) -> dict | None:
    try:
        return json.loads((jdir(k) / "job.json").read_text())
    except (OSError, ValueError):
        return None


def _write(k: str, job: dict) -> None:
    p = jdir(k) / "job.json"; p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(f"job.json.{os.getpid()}.tmp"); tmp.write_text(json.dumps(job, ensure_ascii=False, indent=1))
    os.replace(tmp, p)


@contextlib.contextmanager
def locked(k: str):
    jdir(k).mkdir(parents=True, exist_ok=True)
    with open(jdir(k) / ".lock", "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def git(*a) -> str:
    return subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout


def text_of(k: str, gen: int, part: str, file: str) -> str | None:
    p = jdir(k) / f"g{gen}" / part / file
    return p.read_text() if p.is_file() else None


def dump(node: dict) -> str:
    """a node file's text (tools/merge_delivery.py dump)"""
    return json.dumps(node, indent=1, ensure_ascii=False) + "\n"


def delivery_files(D: dict) -> dict:
    """{path: text} of every file a merge agent may change: the delivery's Lean modules and node files"""
    out = {m["file"]: m["text"] for m in D["modules"]}
    out.update({x["path"]: dump(x["node"]) for x in D["nodes"].values()})
    return out


def is_node(path: str) -> bool:
    return path.startswith("dag/nodes/") and path.endswith(".json")


def spec_of(head: str, kind: str, files: list[dict], modules: dict) -> dict:
    return {"head": head, "kind": kind, "delivery_all": sha(json.dumps(sorted(modules.items()))), "files": sorted(({"file": f["file"], "base_sha": sha(f["base"]), "target_sha": sha(f["target"]),
                                                         "delivery_sha": sha(f["ours"])} for f in files), key=lambda x: x["file"])}


def request(g: str, item: str, head: str, base: str, kind: str, files: list[dict], modules: dict, report: str | None,
            other: dict | None = None) -> dict:
    """Request a job (idempotent: the same spec keeps the job as it is). files: [{file, base, target, ours}] (texts; a
    missing base is ''); modules: delivery_files(D), every file of the delivery the agent may change; other: for `pending`,
    {group, item, head, report} of the delivery the merge goes onto."""
    k = key(g, item)
    spec = spec_of(head, kind, files, modules)
    with locked(k):
        old = read(k)
        if old and old.get("spec") == spec:
            return old
        gen = int((old or {}).get("gen", 0)) + 1
        d = jdir(k) / f"g{gen}"
        shutil.rmtree(d, ignore_errors=True)
        for f in files:
            for part in ("base", "target", "ours"):
                p = d / part / f["file"]; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(f[part] or "")
        for file, text in modules.items():
            if text is not None:
                p = d / "modules" / file; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        if report:
            (d / "ours.report.md").write_text(report)
        if other and other.get("report"):
            (d / "other.report.md").write_text(other["report"])
        job = {"group": g, "item": item, "head": head, "base": base, "kind": kind, "gen": gen, "spec": spec,
               "other": {x: other[x] for x in ("group", "item", "head") if x in other} if other else None,
               "state": "requested", "requested": now(), "attempts": 0, "first_requested": (old or {}).get("first_requested") or now(),
               "history": ((old or {}).get("history") or [])[-6:] + ([f"{now()} gen {old['gen']} ({old.get('state')}) superseded: "
                                                                       + ("new head" if old.get("head") != head else "target or text changed")]
                                                                      if old else [])}
        _write(k, job)
        for x in jdir(k).glob("g*"):
            if x.is_dir() and x.name != f"g{gen}":
                shutil.rmtree(x, ignore_errors=True)
        return job


def resolve(g: str, item: str, head: str, base: str, conflicts: list[dict], modules: dict, report: str | None):
    """check(): the delivery's files in `conflicts` ([{file, base, target (= main's text now), ours}]) changed on main
    since its base. ('merged', {file: text}) | ('failed', why) | ('wait', why); requests the job when none fits."""
    k = key(g, item)
    job = read(k)
    if job and job.get("head") == head:
        jf = {f["file"]: f for f in job["spec"]["files"]}
        if job["spec"].get("delivery_all") == sha(json.dumps(sorted(modules.items()))) and all(
                c["file"] in jf and jf[c["file"]]["target_sha"] == sha(c["target"]) and jf[c["file"]]["delivery_sha"] == sha(c["ours"])
                for c in conflicts):
            # the job (of kind main, or a pending one whose other delivery has landed as expected) fits
            if job["state"] == "failed":
                return "failed", job.get("explanation") or "the merge agent could not merge the changes"
            if job["state"] == "merged":
                out = {f: text_of(k, job["gen"], "merged", f) for f in (job.get("merged_files") or [c["file"] for c in conflicts])}
                if all(t is not None for t in out.values()):
                    return "merged", out
            elif job["state"] in ("requested", "running"):
                return "wait", (f"waits for the merge agent (job {k} gen {job['gen']}, {job['state']}): "
                                + ", ".join(c["file"].rsplit("/", 1)[-1] for c in conflicts) + f" changed on {MAIN} since the base")
    job = request(g, item, head, base, "main", conflicts, modules, report)
    files = ", ".join(c["file"].rsplit("/", 1)[-1] for c in conflicts)
    return "wait", f"waits for the merge agent (job {k} gen {job['gen']}, {job['state']}): {files} changed on {MAIN} since the base"


def request_pending(plans: list[dict], log=None) -> int:
    """The checked deliveries `plans` (check() results in the order the batch takes them) that write the same Lean file:
    the first lands as it is, every later one gets a `pending` job onto the first one's text, unless it already has a
    job of kind `main` for this head (its checked text is a merge onto main; it waits for main as before). Returns the
    number of jobs requested or kept."""
    by = {}
    for x in plans:
        for m in x["D"]["modules"]:
            if m["file"] in x.get("write", []) and m.get("text") is not None and m["file"].endswith(".lean"):
                by.setdefault(m["file"], []).append((x, m))
    per = {}
    for file, xs in by.items():
        if len(xs) < 2:
            continue
        a, am = xs[0]
        for x, m in xs[1:]:
            cur = x["cur"].get(file)
            if a["cur"].get(file) != cur:
                continue        # (both None: two deliveries create the same new module)
            per.setdefault((x["group"], x["item"], x["head"]), (x, a, []))[2].append({"file": file, "base": cur or "", "target": am["text"], "ours": m["text"]})
    n = 0
    for (g, item, head), (x, a, files) in per.items():
        old = read(key(g, item))
        if old and old.get("head") == head and old.get("kind") == "main":
            continue
        try:
            j = request(g, item, head, x["base"], "pending", files, delivery_files(x["D"]),
                        x["D"].get("report"), {"group": a["group"], "item": a["item"], "head": a["head"], "report": a["D"].get("report")})
            n += 1
            if log and (not old or old.get("gen") != j["gen"]):
                log("merge job requested", g, item, head[:9], "| pending: onto", f"{a['group']}/{a['item']}", ", ".join(f["file"] for f in files))
        except Exception as e:  # noqa: BLE001   detection never blocks a landing
            if log:
                log("merge job request failed", g, item, head[:9], "|", repr(e)[:200])
    return n


# ---------------------------------------------------------------- the runner's transitions

def refresh(k: str) -> str:
    """A `main` job whose target file is no longer main's file: requested again with main's text now. Prints the state."""
    job = read(k)
    if not job:
        return "gone"
    head = git("rev-parse", "-q", "--verify", f"refs/heads/deliver/{job['group']}/{job['item']}").strip()
    if head != job["head"]:
        return "stale"
    if job["kind"] != "main" or job["state"] not in ("requested", "running"):
        return job["state"]
    files, moved = [], False
    for f in job["spec"]["files"]:
        p = ROOT / f["file"]
        cur = p.read_text() if p.is_file() else None
        if cur is None:
            return "stale"
        moved |= sha(cur) != f["target_sha"]
        files.append({"file": f["file"], "base": text_of(k, job["gen"], "base", f["file"]), "target": cur,
                      "ours": text_of(k, job["gen"], "ours", f["file"])})
    if not moved:
        return job["state"]
    d = jdir(k) / f"g{job['gen']}"
    mods = job_modules(k, job["gen"])
    rep = (d / "ours.report.md").read_text() if (d / "ours.report.md").is_file() else None
    j = request(job["group"], job["item"], job["head"], job["base"], "main", files, mods, rep)
    return f"re-requested gen {j['gen']} (main changed)"


def job_modules(k: str, gen: int) -> dict:
    """{path: text} of the delivery's files as the job stored them"""
    d = jdir(k) / f"g{gen}" / "modules"
    return {str(p.relative_to(d)): p.read_text() for p in d.rglob("*") if p.is_file()} if d.is_dir() else {}


def start(k: str, gen: int, run: str, pid: str) -> int:
    with locked(k):
        job = read(k)
        if not job or job["gen"] != gen or job["state"] not in ("requested", "running"):
            print("not started: the job changed"); return 1
        job.update(state="running", run=run, pid=int(pid), started=now(), attempts=int(job.get("attempts", 0)) + 1)
        _write(k, job)
    return 0


def retry(k: str, gen: int, why: str) -> int:
    with locked(k):
        job = read(k)
        if not job or job["gen"] != gen:
            return 1
        n = int(job.get("attempts", 0))
        if re.match(r"session (limit|rate|no-token|stopped|auth)", why) or why.startswith("the runner stopped"):
            n = max(0, n - 1)        # the token's or the runner's fault, not the agent's: not counted
        job["history"] = (job.get("history") or [])[-8:] + [f"{now()} gen {gen}: {why[:200]}"]
        if n >= MAX_SESSIONS:
            job.update(state="failed", finished=now(), attempts=n, explanation=(
                f"your delivery's file(s) {', '.join(f['file'] for f in job['spec']['files'])} changed on {MAIN} after your "
                f"base, and {n} merge agent sessions ended without a merge ({why[:300]}). Take the file as it is on {MAIN} "
                "now, make your change in it, compile and deliver again."))
        else:
            job.update(state="requested", attempts=n, not_before=time.time() + RETRY_PAUSE, last_error=why[:500])
        _write(k, job)
    return 0


def _ordered(mods: dict) -> list[str]:
    """module files in import order among themselves"""
    sys.path.insert(0, str(TOOLS))
    import stage2_delivery as s2
    name = {f[len("lean/"):-5].replace("/", "."): f for f in mods}
    done, out = set(), []
    while len(out) < len(mods):
        step = [f for m, f in name.items() if m not in done and all(i in done or i not in name for i in s2.imports(mods[f]))] \
            or [f for m, f in name.items() if m not in done]
        for f in step:
            done.add(f[len("lean/"):-5].replace("/", ".")); out.append(f)
    return out


def verify(job: dict, merged: dict) -> tuple[str, str]:
    """Compile the delivery's Lean modules with the merged files in place, each alone, and, for every Lean file the
    merge changed whose interface differs from main's file, its direct importers outside the delivery
    (tools/importer_compile.py's call of tools/remote_compile_set.py: lean -j1, LEAN_NUM_THREADS=1, 60 s); then the node
    checks (verify_nodes) when a node file is involved. ('green'|'red'|'unknown', evidence)."""
    sys.path.insert(0, str(TOOLS))
    import importer_compile as ic, stage3_delivery as s3, leanindex as li
    k = key(job["group"], job["item"])
    allf = job_modules(k, job["gen"])
    allf.update(merged)
    node_fails = verify_nodes(job, merged, allf)
    mods = {f: t for f, t in allf.items() if f.endswith(".lean") and t is not None}
    own = [(f[len("lean/"):], mods[f], True) for f in _ordered(mods)]
    names = {f[len("lean/"):-5].replace("/", ".") for f in mods}
    imp = []
    for f, text in merged.items():
        if not f.endswith(".lean"):
            continue
        cur = (ROOT / f).read_text() if (ROOT / f).is_file() else None
        if cur is None or not li.interface_changes(cur, text):
            continue        # a module main does not have yet has no importer outside the delivery
        imp += [u for u in s3.importers(f[len("lean/"):-5].replace("/", ".")) if u not in names and u not in imp]
    cap = ic.CAP
    comp, skipped = imp[:cap], imp[cap:]
    deadline = time.time() + ic.BUDGET
    chunks = [comp[i:i + ic.CHUNK] for i in range(0, len(comp), ic.CHUNK)] or [[]]
    res = []
    for ch in chunks:
        jobs = list(own)
        for u in ch:
            try:
                jobs.append((ic.rel_of(u), (ic.LEAN / ic.rel_of(u)).read_text(), False))
            except OSError:
                pass
        res += ic._call(jobs, ic.BUDGET, deadline)
    red_before = ic.failing_last_build()
    lines, seen = [], set()
    own_fail = own_none = imp_fail = False
    for r in res:
        mod = r["rel"][:-5].replace("/", ".")
        if mod in seen:
            continue
        seen.add(mod)
        rc = r.get("rc")
        st = "OK" if rc == 0 else "SLOW" if rc == 124 else "NOT RUN" if rc is None else "FAIL"
        own = mod in names
        lines.append(f"- {'delivery module' if own else 'importer'} {mod}: {st}" + (f" ({r.get('secs')} s)" if r.get("secs") else "")
                     + (" (failing in the last global build too: pre-existing)" if not own and st != "OK" and mod in red_before else ""))
        if st != "OK":
            lines.append("```\n" + (r.get("out") or "").strip()[-2000:] + "\n```")
        if own:
            own_fail |= rc not in (0, None); own_none |= rc is None
        else:
            imp_fail |= rc not in (0, None) and mod not in red_before
    if node_fails:
        lines.append("- DAG node checks (tools/stage3_delivery.py check_nodes, lean records): FAIL\n" + "\n".join("  - " + x for x in node_fails[:20]))
    elif any(is_node(f) for f in merged):
        lines.append("- DAG node checks (tools/stage3_delivery.py check_nodes, lean records): OK")
    state = "red" if own_fail or imp_fail or node_fails else "unknown" if own_none else "green"
    if skipped:
        lines.append(f"- importers not compiled (over the cap {cap}; the global build compiles them): {', '.join(skipped)}")
    return state, "\n".join(lines)


def verify_nodes(job: dict, merged: dict, allf: dict) -> list[str]:
    """The delivery's node files after the merge, through the delivery checks the lander applies
    (tools/stage3_delivery.py check_nodes, against the nodes on main now): a node in conflict lands as a change of main's
    node; every node's `lean` record names a declaration of its (merged) module with the recorded statement. Only when the
    merge involves a node file. Returns the findings."""
    if not any(is_node(f) for f in merged):
        return []
    sys.path.insert(0, str(TOOLS))
    import stage2_delivery as s2, stage3_delivery as s3
    G = s2.Git(ROOT)
    nodes_base = s2.nodes_at(G, MAIN)
    conflict = {f["file"] for f in job["spec"]["files"]}
    D = {"fails": [], "notes": [], "modules": [], "nodes": {}, "changes": {}, "base": job["base"], "users": {}}
    for f, text in allf.items():
        if f.endswith(".lean") and text is not None:
            cur = (ROOT / f).read_text() if (ROOT / f).is_file() else None
            D["modules"].append({"file": f, "module": f[len("lean/"):-5].replace("/", "."), "role": "item", "old": cur,
                                 "text": text, "diff": s3.diff_module(cur, text)})
    fails = []
    for p, text in allf.items():
        if not is_node(p):
            continue
        nid = pathlib.PurePosixPath(p).stem
        try:
            node = json.loads(text)
        except ValueError as e:
            fails.append(f"{p}: not valid JSON ({e})"); continue
        cur = (ROOT / p).read_text() if (ROOT / p).is_file() else None
        if p in conflict and cur is not None:
            bn, role = json.loads(cur), "changed"
        else:
            b = G.show(job["base"], p)
            bn = json.loads(b) if b else None
            role = "new" if bn is None else "changed"
        D["nodes"][nid] = {"path": p, "node": node, "base_node": bn, "role": role}
        if node.get("id") != nid:
            fails.append(f"{p}: id {node.get('id')!r} is not the file name")
        lean = node.get("lean") if isinstance(node.get("lean"), dict) else {}
        lf, decl = lean.get("file"), lean.get("declaration")
        if p in merged and lf and isinstance(decl, str):
            src = allf.get(lf) if lf in allf else ((ROOT / lf).read_text() if (ROOT / lf).is_file() else None)
            if src is None:
                fails.append(f"{p}: lean.file {lf} is neither a file of the delivery nor on {MAIN}")
            else:
                byname = {d["name"]: d for d in s2.declarations(src) if d["name"]}
                if decl not in byname:
                    fails.append(f"{p}: lean.declaration {decl} is not declared in {lf}")
                elif lean.get("statement") and s2.normalize(lean["statement"]) != byname[decl]["statement"]:
                    fails.append(f"{p}: lean.statement differs from the signature of {decl} in {lf}")
    try:
        s3.check_nodes(D, lambda L, x: fails.append(f"({L}) {x}"), G, job["base"], job["group"], job["item"], nodes_base)
    except Exception as e:  # noqa: BLE001
        fails.append(f"the node check could not run: {e!r}"[:300])
    return fails


def finish(k: str, gen: int, run: str, verdict: str, expl_file: str) -> int:
    job = read(k)
    if not job or job["gen"] != gen:
        print("superseded: the job changed during the session"); return 1
    expl = pathlib.Path(expl_file).read_text() if os.path.isfile(expl_file) else ""
    if verdict == "MERGED":
        merged = {}
        for f in job["spec"]["files"]:
            p = pathlib.Path(run) / "merged" / f["file"]
            if not p.is_file():
                retry(k, gen, f"the agent answered MERGED without writing {p}"); print("no merged file"); return 1
            merged[f["file"]] = p.read_text()
        for f, text in job_modules(k, gen).items():      # 2026-10-26: any other file of the delivery the agent changed
            p = pathlib.Path(run) / "merged" / f
            if f not in merged and p.is_file() and p.read_text() != text:
                merged[f] = p.read_text()
        state, ev = verify(job, merged)
        (pathlib.Path(run) / "compile.md").write_text(ev + "\n")
        if state == "unknown":
            retry(k, gen, "the compile service did not compile the merged module: " + ev[:300]); print("compile not run"); return 1
        if state == "red":
            with locked(k):
                j = read(k)
                if not j or j["gen"] != gen:
                    return 1
                if int(j.get("attempts", 1)) < ATTEMPTS:
                    j.update(state="requested", last_compile=ev[-6000:], last_error="the merged file did not compile")
                    j["history"] = (j.get("history") or [])[-8:] + [f"{now()} gen {gen}: attempt {j.get('attempts')} red"]
                    _write(k, j); print("red: another attempt"); return 0
                j.update(state="failed", finished=now(), explanation=(
                    f"the merge agent's merge of your changes with the changes on {MAIN} did not pass the compile and DAG checks (twice):\n{ev[-2500:]}\n"
                    f"Agent's note: {expl[:1500]}"))
                _write(k, j)
            print("red: failed"); return 0
        with locked(k):
            j = read(k)
            if not j or j["gen"] != gen:
                print("superseded"); return 1
            for f, text in merged.items():
                p = jdir(k) / f"g{gen}" / "merged" / f; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
            j.update(state="merged", finished=now(), explanation=expl[:4000], compile=ev[-4000:], run=run, merged_files=sorted(merged))
            _write(k, j)
        print("merged"); return 0
    with locked(k):
        j = read(k)
        if not j or j["gen"] != gen:
            return 1
        j.update(state="failed", finished=now(), run=run, explanation=(
            f"your delivery's file(s) {', '.join(f['file'] for f in j['spec']['files'])} changed on {MAIN} after your base "
            + (f"(onto the waiting delivery {j['other']['group']}/{j['other']['item']}) " if j.get("other") else "")
            + f"and the merge agent could not keep both changes: {expl[:2500]}\nTake the file as it is on {MAIN} now, make "
            "your change in it, compile and deliver again."))
        _write(k, j)
    print("failed"); return 0


def gc() -> int:
    n = 0
    for p in JOBS.glob("*/job.json"):
        try:
            job = json.loads(p.read_text())
        except (OSError, ValueError):
            continue
        head = git("rev-parse", "-q", "--verify", f"refs/heads/deliver/{job['group']}/{job['item']}").strip()
        if head == job["head"]:
            continue
        if time.time() - p.stat().st_mtime > 7200:
            shutil.rmtree(p.parent, ignore_errors=True); n += 1
    return n


def live_jobs() -> list[dict]:
    heads = {}
    for l in git("for-each-ref", "--format=%(refname:short) %(objectname)", "refs/heads/deliver").splitlines():
        r, h = l.split(" "); heads[r[len("deliver/"):]] = h
    out = []
    for p in sorted(JOBS.glob("*/job.json")):
        try:
            job = json.loads(p.read_text())
        except (OSError, ValueError):
            continue
        if heads.get(f"{job['group']}/{job['item']}") == job["head"]:
            out.append(job)
    return out


def status(as_json: bool) -> int:
    c = {}
    for j in live_jobs():
        c[j["state"]] = c.get(j["state"], 0) + 1
    if as_json:
        print(json.dumps(c)); return 0
    print("merge jobs (deliveries waiting for a merge agent):", ", ".join(f"{s} {n}" for s, n in sorted(c.items())) or "none")
    return 0


# ---------------------------------------------------------------- dry run

IMPORT_LINE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")


def _imports_only(old, now_):
    if old is None or now_ is None or old == now_:
        return False
    ol = old.split("\n"); have = {l.strip() for l in ol}
    added, rest = [], []
    for l in now_.split("\n"):
        (added if IMPORT_LINE.match(l) and l.strip() not in have else rest).append(l)
    return bool(added) and rest == ol


def scan() -> int:
    """Read only: every stage-3 delivery branch held by its group: its Lean files that changed on main since its base
    (kind main), and the Lean files two waiting deliveries both write (kind pending)."""
    heads = {}
    for l in git("for-each-ref", "--format=%(refname:short) %(objectname)", "refs/heads/deliver").splitlines():
        r, h = l.split(" "); p = r.split("/")
        if len(p) == 3 and "." in p[2]:
            heads[(p[1], p[2])] = h
    writers, nmain, ndel = {}, 0, 0
    for (g, item), head in sorted(heads.items()):
        try:
            who = json.loads((ROOT / "coord" / "claims" / f"{item}.lock").read_text()).get("who")
        except (OSError, ValueError):
            who = None
        if who != g:
            continue
        passed = (ROOT / "local" / "batch" / "passed" / f"{g}__{item}.json")
        try:
            passed = json.loads(passed.read_text()).get("head") == head
        except (OSError, ValueError):
            passed = False
        ndel += 1
        base = git("merge-base", MAIN, head).strip()
        for f in git("diff", "--name-only", base, head, "--", "lean/").split():
            if not f.endswith(".lean"):
                continue
            ours = subprocess.run(["git", "show", f"{head}:{f}"], cwd=ROOT, capture_output=True, text=True)
            ours = ours.stdout if ours.returncode == 0 else None
            b = subprocess.run(["git", "show", f"{base}:{f}"], cwd=ROOT, capture_output=True, text=True)
            b = b.stdout if b.returncode == 0 else None
            p = ROOT / f
            cur = p.read_text() if p.is_file() else None
            if cur == ours:
                continue
            writers.setdefault(f, []).append(f"{g}/{item}")
            if cur != b and not _imports_only(b, cur):
                nmain += 1
                by = git("log", "--format=%h %s", f"{base}..{MAIN}", "--", f).splitlines()
                print(f"main\t{g}/{item}\t{head[:9]}\t{'passed' if passed else 'auto/review'}\t{f}\t{len(by)} commit(s): {'; '.join(x[:70] for x in by[:2])}")
    npend = 0
    for f, ws in sorted(writers.items()):
        if len(ws) > 1:
            npend += 1
            print(f"pending\t{f}\t{' '.join(ws)}")
    print(f"# {ndel} delivery branches held by their group; {nmain} file(s) changed on main since the delivery's base; "
          f"{npend} file(s) written by two or more waiting deliveries")
    return 0


def main(a: list[str]) -> int:
    if a == ["scan"]:
        return scan()
    if a and a[0] == "status":
        return status("--json" in a)
    if len(a) == 2 and a[0] == "refresh":
        print(refresh(a[1])); return 0
    if len(a) == 5 and a[0] == "start":
        return start(a[1], int(a[2]), a[3], a[4])
    if len(a) == 6 and a[0] == "finish":
        return finish(a[1], int(a[2]), a[3], a[4], a[5])
    if len(a) >= 4 and a[0] == "retry":
        return retry(a[1], int(a[2]), " ".join(a[3:]))
    if a == ["gc"]:
        print(gc()); return 0
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
