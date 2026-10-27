#!/usr/bin/env python3
"""Merge agents for the conflicts of an upstream sync (the owner, 2026-10-23: "a sync is a real merge, never an
overwrite; keep what most deserves keeping; what is local goes to the PR agent").

The scheduled sync (~/cc1/upsync-quick.py) merges every file the source changed three-way (tools/upstream_merge.py:
base = coord/upstream-base.txt, ours = live, theirs = the new tip); the hunks that do not overlap merge by themselves.
This tool handles the files where both sides changed the same lines, BEFORE the sync takes its locks:

  run      copy live lean/ to <work>/tree (rsync, no .lake), run `tools/upstream_merge.py apply` there, and for every
           file left in conflict start one merge agent (`claude -p`, model claude-opus-5-5, token from the pool
           ~/weil-review-svc/tokenpool.py, like ~/cc1/pr-agent/loop.py) on <work>/tree/lean/<P>, which holds the diff3
           text with conflict markers. The agent resolves it by the brief below, compiles it with `compile` and writes
           <work>/tasks/<module>/result.json and record.md. Then this tool checks the result itself: no conflict
           marker, compiles (its own compile, not the agent's word), no upstream declaration lost, no upstream
           statement changed (except a recorded correction of a false upstream statement), none of our declarations
           dropped without a reason, no proof lost unless declared as a regression. An accepted file goes to the
           standing resolutions ~/upstream-sync/resolved/<P> + index.tsv (keyed by our blob and the tip's blob), which
           `tools/upstream_merge.py apply --resolved` then uses in the live merge. <work>/agents.json lists every
           file: accepted (with the agent's record and any declared regressions) or not (with the reason).
  compile  compile one file of a merge tree, single core, against the live published build: the modules of its import
           closure whose text differs from the published commit (the merged neighbours) are compiled first in a
           private overlay, through ~/cc1/rset.py (the shared compile slot pool, lean -j1, LEAN_NUM_THREADS=1).
           At most UPMERGE_COMPILES (2) such calls at once.

A file whose agent fails is not in the resolutions: the sync gives it the tip's text and keeps ours in
coord/preferred-upstream/<module>.{lean,md} for the worker of that module (never silently dropped).

  tools/upstream_merge_agent.py run <base> <tip> --source-git DIR --work DIR [--parallel N] [--budget S] [--only P,P]
                                    [--resolved DIR] [--no-agent]
  tools/upstream_merge_agent.py compile <lean-relative path> --tree DIR [--timeout S]
Env: UPMERGE_COMPILES (2), UPMERGE_MAX_DEPS (120), UPMERGE_AGENT_TIMEOUT (3600 s), UPMERGE_MODEL (claude-opus-5-5).
"""
from __future__ import annotations
import sys as _sys
_here = _sys.path.pop(0) if _sys.path and _sys.path[0].endswith("tools") else None   # tools/queue.py shadows `queue`
import queue as _queue, concurrent.futures.thread  # noqa: E401,F401
if _here is not None:
    _sys.path.insert(0, _here)
import concurrent.futures as cf, fcntl, hashlib, io, json, os, pathlib, re, shutil, subprocess, sys, tarfile, time

TOOLS = pathlib.Path(__file__).resolve().parent
ROOT = TOOLS.parent                                   # the live repository (or a test copy)
H = pathlib.Path.home()
LIVE = H / "weil-conjectures-sheaf"                    # whose published build every compile uses
sys.path.insert(0, str(TOOLS))
RESOLVED = H / "upstream-sync" / "resolved"
SLOTS = H / "upstream-sync" / "merge-compile-slots"
NCOMP = int(os.environ.get("UPMERGE_COMPILES", "2"))
MAX_DEPS = int(os.environ.get("UPMERGE_MAX_DEPS", "120"))
AGENT_TIMEOUT = int(os.environ.get("UPMERGE_AGENT_TIMEOUT", "3600"))
MODEL = os.environ.get("UPMERGE_MODEL", "claude-opus-5-5")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)
MARKER = re.compile(r"^(<<<<<<< |\|\|\|\|\|\|\| |=======$|>>>>>>> )", re.M)
PROJECT = ("Sheaf", "WeilConjectures")


def say(*a):
    print(time.strftime("%F %T"), "[merge-agent]", *a, flush=True)


def git(*a, cwd=ROOT, text=True, check=True, inp=None):
    r = subprocess.run(["git", *a], cwd=cwd, capture_output=True, text=text, input=inp)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(a[:3])}: {(r.stderr or '').strip()[-300:]}")
    return r.stdout


def mod_of(rel: str) -> str:
    return rel[:-5].replace("/", ".")


def rel_of(mod: str) -> str:
    return mod.replace(".", "/") + ".lean"


# ------------------------------------------------------------------------------------------------ compile

def published_commit() -> str:
    return json.loads((LIVE / "local" / "builds" / "published.json").read_text())["commit"]


def cat_blobs(commit: str, rels: list[str]) -> dict[str, bytes | None]:
    """{rel: bytes of lean/<rel> at commit or None}, one git process"""
    if not rels:
        return {}
    r = subprocess.run(["git", "cat-file", "--batch"], cwd=LIVE, capture_output=True,
                       input="".join(f"{commit}:lean/{x}\n" for x in rels).encode()).stdout
    out, off = {}, 0
    for x in rels:
        e = r.index(b"\n", off); head = r[off:e].split()
        if len(head) == 2 and head[1] == b"missing":
            out[x] = None; off = e + 1; continue
        size = int(head[2]); out[x] = r[e + 1:e + 1 + size]; off = e + 1 + size + 1
    return out


def stale_closure(tree: pathlib.Path, rel: str) -> tuple[list[str], int]:
    """the modules of rel's import closure (in tree/lean) that must be compiled before it, in import order: those whose
    text differs from the published commit, and those importing one of them. Returns (rels, size of the closure)."""
    lean = tree / "lean"
    imps: dict[str, list[str]] = {}
    todo, seen = [rel], set()
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen.add(x)
        f = lean / x
        if not f.is_file():
            imps[x] = []; continue
        ms = [m for m in IMPORT.findall(f.read_text(errors="ignore")) if m.split(".")[0] in PROJECT]
        imps[x] = [rel_of(m) for m in ms if (lean / rel_of(m)).is_file()]
        todo += imps[x]
    pub = cat_blobs(published_commit(), sorted(seen - {rel}))
    dirty = {x for x in seen - {rel} if pub.get(x) != (lean / x).read_bytes()}
    need: dict[str, bool] = {}

    def needs(x, stack=()):
        if x in need:
            return need[x]
        if x in stack:
            return False
        need[x] = x in dirty or any(needs(y, stack + (x,)) for y in imps.get(x, []))
        return need[x]
    order, done = [], set()

    def visit(x, stack=()):
        if x in done or x in stack:
            return
        for y in imps.get(x, []):
            visit(y, stack + (x,))
        done.add(x)
        if x != rel and needs(x):
            order.append(x)
    visit(rel)
    return order, len(seen)


class Slot:
    """one of NCOMP lock files: at most NCOMP compile calls of merge agents at once"""
    def __enter__(s):
        SLOTS.mkdir(parents=True, exist_ok=True)
        while True:
            for i in range(NCOMP):
                s.f = open(SLOTS / f"{i}.lock", "w")
                try:
                    fcntl.flock(s.f, fcntl.LOCK_EX | fcntl.LOCK_NB); return s
                except BlockingIOError:
                    s.f.close()
            time.sleep(5)

    def __exit__(s, *e):
        fcntl.flock(s.f, fcntl.LOCK_UN); s.f.close()


def compile_file(tree: pathlib.Path, rel: str, timeout: int = 300) -> tuple[int, str]:
    """(rc, text): rc 0 when rel compiles (after its stale neighbours)"""
    deps, n = stale_closure(tree, rel)
    note = ""
    if len(deps) > MAX_DEPS:
        note = (f"NOTE: {len(deps)} modules of the import closure differ from the published build (more than "
                f"{MAX_DEPS}); compiled against the published build only, errors about them may be stale.\n")
        deps = []
    jobs = [{"rel": x, "out": True} for x in deps] + [{"rel": rel, "out": True}]
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as t:
        man = json.dumps({"jobs": jobs, "timeout": timeout, "stop_on_fail": True}).encode()
        ti = tarfile.TarInfo("manifest.json"); ti.size = len(man); t.addfile(ti, io.BytesIO(man))
        for j in jobs:
            t.add(str(tree / "lean" / j["rel"]), arcname="lean/" + j["rel"])
    data = buf.getvalue()
    for attempt in range(6):
        with Slot():
            p = subprocess.run(["python3", str(H / "cc1" / "rset.py")], input=data, capture_output=True,
                               env=dict(os.environ, LEAN_NUM_THREADS="1"))
        if p.returncode == 75:
            time.sleep(30); continue
        break
    if p.returncode:
        return 2, note + f"compile service failed (exit {p.returncode}): {p.stderr.decode(errors='replace')[-800:]}"
    with tarfile.open(fileobj=io.BytesIO(p.stdout), mode="r:gz") as t:
        res = json.loads(t.extractfile("result.json").read())["results"]
    out = [note] if note else []
    if deps:
        out.append(f"{len(deps)} merged neighbour(s) compiled first: {', '.join(mod_of(x) for x in deps[:30])}"
                   + (" ..." if len(deps) > 30 else "") + "\n")
    rc = 0
    for r in res:
        if r["rel"] != rel and r["rc"] == 0:
            continue
        o = r.get("out")
        out.append(f"== {r['rel']}: exit {r['rc']} ({r.get('secs')} s)\n" + (o if o is not None else f"timeout after {timeout} s\n"))
        if r["rc"]:
            rc = r["rc"] if r["rel"] == rel else 3
    if not any(r["rel"] == rel for r in res):
        rc = rc or 3
        out.append(f"== {rel}: not compiled (a neighbour failed first)\n")
    return rc, "".join(out)


# ------------------------------------------------------------------------------------------------ checks

def exceptions() -> list[tuple[str, str, str]]:
    p = ROOT / "coord" / "upstream-statement-exceptions.tsv"
    out = []
    for l in p.read_text().splitlines() if p.exists() else []:
        c = l.split("\t")
        if l.strip() and not l.startswith("#") and len(c) >= 3:
            out.append((c[0], c[1], c[2]))
    return out


def decls(text: str) -> dict[str, dict]:
    import stage2_delivery as s2
    out = {}
    for d in s2.declarations(text):
        k = d["name"] or "instance " + " ".join((d["statement"] or "").split())
        out[k] = d
    return out


def norm(s) -> str:
    return " ".join((s or "").split())


def n_sorry(body: str) -> int:
    return len(re.findall(r"(?<![\w'])sorry(?![\w'])", re.sub(r"--[^\n]*|/-.*?-/", "", body or "", flags=re.S)))


def check(mod: str, ours: str | None, tip: str | None, res: str, declared: dict, base: str = "") -> list[str]:
    """reasons to reject an agent's resolution (empty: accepted)"""
    bad = []
    if MARKER.search(res):
        return ["conflict markers left in the file"]
    try:
        do, dt, dr = decls(ours or ""), decls(tip or ""), decls(res)
        db = decls(base or "")
    except Exception as e:   # noqa: BLE001
        return [f"declarations not readable: {e!r}"[:200]]
    false_rows = {e for m, e, why in exceptions() if m == mod and "false upstream" in why}
    any_rows = {e for m, e, why in exceptions() if m == mod}
    short = lambda k: k.split(".")[-1]
    in_rows = lambda k, rows: k in rows or short(k) in {short(x) for x in rows}
    dropped_ok = set(declared.get("dropped_ours") or {}) | set(declared.get("dropped_upstream") or {})
    for k, d in dt.items():
        if k.startswith("instance "):
            continue
        if k not in dr:
            # we had removed it before this sync and upstream did not change it: our earlier change, kept by the merge
            if k not in do and k in db and norm(db[k]["statement"]) == norm(d["statement"]) \
                    and norm(db[k]["body"]) == norm(d["body"]):
                continue
            if not in_rows(k, any_rows) and k not in dropped_ok and short(k) not in {short(x) for x in dropped_ok}:
                bad.append(f"upstream declaration {k} missing")
            continue
        if norm(dr[k]["statement"]) != norm(d["statement"]):
            if not (k in do and norm(dr[k]["statement"]) == norm(do[k]["statement"]) and in_rows(k, false_rows)):
                bad.append(f"statement of upstream {k} changed (only a recorded correction of a false upstream statement may)")
    for k, d in do.items():
        if k.startswith("instance ") or k in dt:
            continue
        if k not in dr and k not in dropped_ok and short(k) not in {short(x) for x in dropped_ok}:
            bad.append(f"our declaration {k} dropped without a reason (result.json dropped_ours)")
    regress = set(declared.get("regressions") or {})
    for k, d in dr.items():
        sides = [x[k] for x in (do, dt) if k in x and norm(x[k]["statement"]) == norm(d["statement"])]
        if sides and n_sorry(d["body"]) > min(n_sorry(x["body"]) for x in sides) and k not in regress \
                and short(k) not in {short(x) for x in regress}:
            bad.append(f"{k} has more sorry than the better side and is not declared in result.json regressions")
    return bad


# ------------------------------------------------------------------------------------------------ agent

BRIEF = """# Upstream sync merge agent (Weil project)

You resolve ONE file of a three-way merge between the upstream library (slopmaster2 of
formal-arithmetic-geometry/weil-conjectures) and our live project. The owner's rule: a sync is a real merge, never an
overwrite; keep what most deserves keeping; what is local is sent upstream later by our PR agent.

File: `{tree}/lean/{rel}` (module `{mod}`). It now holds the diff3 merge: `<<<<<<< ours` (our live text),
`||||||| base` (upstream at the last sync, {base9}), `=======`, `>>>>>>> source` (upstream's new tip, {tip9}).
The hunks outside the markers are already merged. Conflict kinds found: {kinds}.
Full versions for reference (read only): `{task}/ours.lean`, `{task}/base.lean`, `{task}/theirs.lean`.
Context: `{task}/context.md` (upstream commits touching the file, our recent commits, rows of the exceptions file).
The rest of the merged library is in `{tree}/lean/` (read only for you).

## How to decide
- Upstream statements and definitions win, unless ours is a recorded correction of a FALSE upstream statement
  (a row of coord/upstream-statement-exceptions.tsv for this module whose reason says "false upstream statement";
  they are in context.md): then our statement stays. Never weaken a statement; never change a statement of upstream
  otherwise.
- Proofs: keep the version that proves more. A proof beats a `sorry`: ours if upstream still has `sorry` there,
  upstream's if it proves what we had as `sorry`. When both prove it, take upstream's unless ours is needed (e.g. a
  performance fix of ours); when upstream changed the statement, our proof must be adapted to the new statement (or the
  declaration keeps upstream's text if it cannot be).
- Keep both sides' new declarations (our helper lemmas, our extra instances, upstream's new material). Drop one of ours
  only when it is now a duplicate of upstream's (same content under upstream's name) or cannot exist any more; list
  each such drop with its reason. A RENAMED declaration counts as dropped under its old name: list it too.
- Imports: upstream's imports plus ours that are still needed. An `import Sheaf.*` inside an upstream file is allowed
  here (the PR agent removes it when sending upstream); keep it when our proof needs it.
- {deleted_note}
- Edit ONLY `{tree}/lean/{rel}` (and files under `{task}/`). Never touch `/home/ubuntu/weil-conjectures-sheaf`
  (the live project), never run lake, tools/build.py or a global build.

## Compile and fix
Compile the file with (single core, against the published build plus the merged neighbours; a call can take minutes):
    python3 {tool} compile {rel} --tree {tree}
Fix until it compiles without errors (warnings are fine; no new `sorry`). If an error comes from a neighbour module
(not this file), say so in result.json and stop. Do at most ~15 compile rounds.

## Output (required)
1. The resolved file at `{tree}/lean/{rel}`, without any conflict marker.
2. `{task}/record.md`: 3-10 lines: each conflict and how it was resolved (which side, why), what was adapted.
3. `{task}/result.json`: {{"status": "resolved" | "unresolved", "compiled": true|false,
   "dropped_ours": {{"<declaration>": "reason"}}, "dropped_upstream": {{"<declaration>": "reason"}},
   "regressions": {{"<declaration>": "a proof of one side that the result does not keep, and why"}},
   "reason": "one line (for unresolved: why)"}}
   Use "unresolved" when you cannot produce a compiling file that respects the rules above; the sync then gives the
   file upstream's text and hands our version to the worker of the module. Never fake a resolution.
"""


def context_md(task: pathlib.Path, up: str, base: str, tip: str, rel: str, mod: str, rows: list) -> str:
    log_up = git("log", "--format=%h %ci %s", f"{base}..{tip}", "--", rel, cwd=up, check=False)[:4000]
    log_us = git("log", "-12", "--format=%h %ci %s", "--", "lean/" + rel, check=False)[:4000]
    ex = "\n".join("\t".join(r) for r in rows) or "(none)"
    return (f"# Context of {mod}\n\n## Upstream commits touching it ({base[:9]}..{tip[:9]})\n\n{log_up or '(none)'}\n\n"
            f"## Our recent commits touching lean/{rel}\n\n{log_us or '(none)'}\n\n"
            f"## Rows of coord/upstream-statement-exceptions.tsv for this module\n\n{ex}\n")


def merge3(ours: bytes, base: bytes, theirs: bytes) -> tuple[int, bytes]:
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        ps = []
        for n, x in (("ours", ours), ("base", base), ("theirs", theirs)):
            (pathlib.Path(d) / n).write_bytes(x); ps.append(str(pathlib.Path(d) / n))
        r = subprocess.run(["git", "merge-file", "-p", "--diff3", "-L", "ours", "-L", "base", "-L", "source", *ps],
                           capture_output=True)
        return r.returncode, r.stdout


def run_agent(task: pathlib.Path, prompt: str) -> tuple[str, str]:
    sys.path.insert(0, str(H / "weil-review-svc"))
    import tokenpool as tp
    for attempt in range(3):
        kind, detail, obj, lease = tp.run_claude(prompt, str(task), "upsync-merge", model=MODEL, timeout=AGENT_TIMEOUT,
                                                 out_path=str(task / f"agent-{attempt}.json"),
                                                 err_path=str(task / f"agent-{attempt}.err"))
        if kind is None:          # no token free: wait
            time.sleep(120); continue
        if (task / "result.json").exists() or kind not in ("limited", "error"):
            return str(kind), str(detail)[:300]
    return "none", "no agent run finished"


def run(a: list[str]) -> int:
    base, tip = a[1], a[2]
    opt = dict(zip(a[3::2], a[4::2]))
    up, work = opt["--source-git"], pathlib.Path(opt["--work"])
    resolved = pathlib.Path(opt.get("--resolved", str(RESOLVED)))
    parallel = int(opt.get("--parallel", "3")); budget = float(opt.get("--budget", "5400"))
    only = set(filter(None, opt.get("--only", "").split(",")))
    no_agent = "--no-agent" in a
    t0 = time.time()
    tree = work / "tree"; tasks = work / "tasks"
    (tree / "lean").mkdir(parents=True, exist_ok=True); tasks.mkdir(exist_ok=True)
    tip = git("rev-parse", tip, cwd=up).strip(); base = git("rev-parse", base, cwd=up).strip()
    # the live lean/ sources as they are now (no build products)
    subprocess.run(["rsync", "-a", "--delete", "--exclude", ".lake", "--exclude", "*.upstream-new",
                    str(ROOT / "lean") + "/", str(tree / "lean") + "/"], check=True)
    r = subprocess.run(["python3", str(TOOLS / "upstream_merge.py"), "apply", base, tip, "--source-git", up,
                        "--resolved", str(resolved), "--json", str(work / "merge.json")],
                       capture_output=True, text=True, env=dict(os.environ, UPSTREAM_MERGE_ROOT=str(tree)))
    (work / "merge.txt").write_text(r.stdout + r.stderr)
    if r.returncode not in (0, 3):
        say("upstream_merge.py apply failed:", (r.stderr or r.stdout)[-500:]); return 2
    rep = json.loads((work / "merge.json").read_text())
    conf = [f for f in rep["files"] if f["class"] == "conflict" and f["path"].endswith(".lean")
            and (not only or f["path"] in only)]
    blob = lambda sha: git("cat-file", "blob", sha, cwd=up, text=False) if sha else b""
    # a module still quarantined (coord/rework.tsv) whose upstream file changed: its quarantined copy is "ours"
    qrows = {}
    rw = ROOT / "coord" / "rework.tsv"
    for l in rw.read_text().splitlines() if rw.exists() else []:
        c = l.split("\t")
        if l.strip() and not l.startswith("#") and len(c) > 2:
            qrows[c[0]] = c[2]
    quar = {}
    for f in rep["files"]:
        q = qrows.get(mod_of(f["path"])) if f["path"].endswith(".lean") else None
        if f["class"] == "deleted-here" and q and f.get("tip") and f.get("base") and (ROOT / q).is_file() \
                and (not only or f["path"] in only):
            ours_q = (ROOT / q).read_bytes()
            if merge3(ours_q, blob(f["base"]), blob(f["tip"]))[0] != 0:
                quar[f["path"]] = ours_q
                conf.append(dict(f, quarantined=q, conflicts=[{"kind": "quarantined copy"}]))
    say(f"{base[:9]}..{tip[:9]}: {len(conf)} file(s) in conflict ({len(quar)} of them quarantined copies): "
        + ", ".join(f["path"] for f in conf))
    rows = exceptions()
    jobs = []
    for f in conf:
        rel = f["path"]; mod = mod_of(rel)
        task = tasks / mod
        if task.exists():
            shutil.rmtree(task)
        task.mkdir(parents=True)
        dst = tree / "lean" / rel
        ours = quar[rel] if rel in quar else (dst.read_bytes() if dst.is_file() else b"")
        b, t = blob(f.get("base")), blob(f.get("tip"))
        (task / "ours.lean").write_bytes(ours); (task / "base.lean").write_bytes(b); (task / "theirs.lean").write_bytes(t)
        kinds = sorted({c["kind"] for c in f.get("conflicts") or []})
        if f.get("tip") and ours:
            dst.parent.mkdir(parents=True, exist_ok=True); dst.write_bytes(merge3(ours, b, t)[1])
        deleted_note = ("Upstream DELETED this file (conflict kind deleted-by-source); the file holds our version. If "
                        "upstream moved its content elsewhere, carry our improvements there only if that file is this one; "
                        "otherwise keep our file when our modules still import it (status resolved) or write "
                        "\"status\": \"delete\" in result.json when nothing of ours needs it."
                        if not f.get("tip") else "The file exists on both sides.")
        if rel in quar:
            deleted_note = (f"This module is QUARANTINED in live (`{f['quarantined']}`, coord/rework.tsv): it failed the "
                            "global build before this sync and a worker will repair it. Resolve the merge by the same "
                            "rules. Compile it and fix what you can; if it still fails for reasons outside this merge "
                            "(its quarantine cause, a quarantined import), that is acceptable: set \"compiled\": false "
                            "and summarize the remaining errors in \"reason\", status resolved.")
        (task / "context.md").write_text(context_md(task, up, base, tip, rel, mod, [r_ for r_ in rows if r_[0] == mod]))
        prompt = BRIEF.format(tree=tree, rel=rel, mod=mod, base9=base[:9], tip9=tip[:9], kinds=", ".join(kinds) or "-",
                              task=task, tool=TOOLS / "upstream_merge_agent.py", deleted_note=deleted_note)
        (task / "prompt.md").write_text(prompt)
        jobs.append((f, task, prompt, ours, t))
    results = {}

    def evaluate(f, task, ours, t, kind, detail):
        """(final, out): the driver's verdict on the agent's output; final False = worth one retry"""
        rel = f["path"]; mod = mod_of(rel)
        try:
            declared = json.loads((task / "result.json").read_text())
        except (OSError, ValueError):
            return True, {"accepted": False, "reason": f"no result.json from the agent ({kind}: {detail})"}
        record = (task / "record.md").read_text() if (task / "record.md").exists() else ""
        out = {"agent": kind, "declared": declared, "record": record}
        st = declared.get("status")
        dst = tree / "lean" / rel
        if st == "delete" and not f.get("tip"):
            out.update(accepted=True, delete=True); return True, out
        if st != "resolved" or not dst.is_file():
            out.update(accepted=False, reason="agent: " + str(declared.get("reason") or st)[:300]); return True, out
        res = dst.read_text(errors="replace")
        bad = check(mod, ours.decode(errors="replace"), t.decode(errors="replace") if f.get("tip") else None, res, declared,
                    base=(task / "base.lean").read_text(errors="replace"))
        if bad:
            out.update(accepted=False, reason="; ".join(bad)[:600]); return False, out
        rc, text = compile_file(tree, rel)
        (task / "final-compile.txt").write_text(text)
        if f.get("quarantined"):
            # a quarantined module need not compile (the worker of its rework item repairs it); kept for the sync
            qd = work / "quarantine-resolved" / rel; qd.parent.mkdir(parents=True, exist_ok=True); qd.write_text(res)
            out.update(accepted=True, quarantined=f["quarantined"], file=str(qd), compiled=rc == 0,
                       ours_sha=hashlib.sha256(ours).hexdigest()); return True, out
        if rc:
            out.update(accepted=False, reason=f"does not compile (exit {rc}): " + text[-400:]); return False, out
        out.update(accepted=True, sha=hashlib.sha256(res.encode()).hexdigest()); return True, out

    def one(job):
        f, task, prompt, ours, t = job
        rel = f["path"]
        if no_agent:
            return rel, {"accepted": False, "reason": "agents disabled (--no-agent)"}
        if time.time() - t0 > budget:
            return rel, {"accepted": False, "reason": f"merge-agent budget of {budget:.0f} s used up before this file"}
        kind, detail = run_agent(task, prompt)
        final, out = evaluate(f, task, ours, t, kind, detail)
        if not final and time.time() - t0 < budget:
            # one more round: the agent sees why the sync's checks refused its result
            say(f"{rel}: refused ({out['reason'][:200]}); one more agent round")
            (task / "first-refusal.txt").write_text(out["reason"])
            (task / "result.json").unlink(missing_ok=True)
            kind, detail = run_agent(task, prompt + "\n\n## Your previous result was REFUSED by the sync's checks\n\n"
                                     + out["reason"] + "\n\nThe file still holds your previous resolution. Fix it (or "
                                     "list each deliberately dropped or renamed declaration in result.json with its "
                                     "reason), compile again, and write record.md and result.json again.\n")
            final, out = evaluate(f, task, ours, t, kind, detail)
            out["retried"] = True
        return rel, out

    with cf.ThreadPoolExecutor(max_workers=max(1, parallel)) as ex:
        for rel, out in ex.map(one, jobs):
            results[rel] = out
            say(f"{rel}: {'ACCEPTED' if out.get('accepted') else 'not resolved: ' + out.get('reason', '')[:200]}")
    # accepted files become standing resolutions for exactly this (our blob, tip blob) pair
    idx = resolved / "index.tsv"
    lines = []
    for f, task, prompt, ours, t in jobs:
        rel = f["path"]; out = results.get(rel, {})
        if not out.get("accepted"):
            continue
        if out.get("delete") or out.get("quarantined"):
            continue          # applied by the sync itself (a deletion; a quarantined copy: <work>/quarantine-resolved)
        dst = resolved / rel; dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tree / "lean" / rel, dst)
        why = f"merge agent {time.strftime('%F')} for {base[:9]}..{tip[:9]}: " + \
            re.sub(r"\s+", " ", str(out["declared"].get("reason") or out.get("record", "")[:200]))[:300]
        lines.append(f"{rel}\t{f['ours'] or ''}\t{f['tip'] or ''}\t{why}\n")
    if lines:
        with open(idx, "a") as fh:
            fh.writelines(lines)
    summary = {"base": base, "tip": tip, "conflicts": len(conf), "seconds": round(time.time() - t0),
               "files": results}
    (work / "agents.json").write_text(json.dumps(summary, indent=1))
    say(f"{sum(1 for x in results.values() if x.get('accepted'))} of {len(conf)} accepted in {time.time() - t0:.0f} s")
    return 0


def main() -> int:
    a = sys.argv[1:]
    if a and a[0] == "compile" and len(a) >= 2:
        opt = dict(zip(a[2::2], a[3::2]))
        rc, text = compile_file(pathlib.Path(opt.get("--tree", str(ROOT))).resolve(), a[1], int(opt.get("--timeout", "300")))
        print(text); print(f"RESULT: exit {rc}")
        return rc
    if a and a[0] == "run" and len(a) >= 3:
        return run(a)
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main())
