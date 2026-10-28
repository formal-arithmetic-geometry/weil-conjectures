#!/usr/bin/env python3
"""Batch landing of stage-3 deliveries (decision of the human, 2026-10-12): deliveries land together, without a compile
on the server, and the global build is the judge.

A group's delivery tool compiles every module of a delivery with the probe on the group's machine before it pushes
the branch. The server does not compile the delivery again. One cycle:

  1. Take every delivery branch deliver/<G>/<module> that needs no reader (tools/review_class.py: AUTO, including
     `compiler-only`) and every delivery a reader passed (tools/merge_delivery.py <G> <module> --stage 3 ... records the
     pass in local/batch/passed/; this tool lands it).
  2. Without any lock, several deliveries at once: the static checks a-e of tools/stage3_delivery.py, the class again
     for reviewer AUTO, the base's age, the commit of the delivery tool (`Prove <module> (<G>)`: the tool pushes only
     what it compiled), every delivered file unchanged in the library since the delivery's base, and
     tools/import_prune_check.py for every module against the library with the delivery's files in place.
     A delivery the checks refuse goes back to its group with the message (coord/returns/<G>.md). The prune check
     reads the library through an index the lander keeps per tip (local/batch/library-index.pkl across restarts).
     A batch takes the deliveries checked so far once no check has finished for SHEAF_BATCH_QUIET s (30), at most
     SHEAF_BATCH_MAX (150) of them; the other checks go on and a later batch takes them (2026-10-18).
  3. Two deliveries that write the same file do not land in one batch: the later one waits for the next cycle.
     Merge agents, not text merges (the human, 2026-10-26; tools/merge_jobs.py): a delivery whose Lean file changed on
     the main branch since its base waits (neither refused nor landed) for a merge job of lane M of the cc review service
     (~/weil-review-svc/mergelane.py), which writes a merge that keeps both intents and compiles it alone with its
     importers; green: the merged text lands in place of the delivery's; not mergeable: the delivery goes back to its
     group with the agent's explanation. Two checked deliveries writing the same Lean file get a job at once (the later
     one is merged onto the first one's text while that one waits to land). The agent may change any file of the
     delivery (its other modules, its node files); DAG node conflicts (a node the delivery creates exists now, or both
     changed the same node field) are merge jobs too, checked by tools/stage3_delivery.py check_nodes (2026-10-26 evening).
  4. Under coord/.merge.lock, held only for the writes: for each delivery, the head and the library files are compared
     with what was checked (a difference: the delivery waits and is checked again), then the files are written and
     registered as one landing (tools/landing.py; several modules are one set), the node records, change records,
     report, claim, ledger line are written as tools/merge_delivery.py --stage 3 wrote them, and one commit
     `Prove <module> (<G>, reviewed by <ID>)` is made. The queue is rewritten once.
  5. The global build (tools/build.py) verifies the whole batch. For the landings of a batch it also enforces what the
     compile of each delivery enforced before: no file slower than SHEAF_FILE_TIMEOUT, no axiom beyond the three, no
     `sorry` the text check did not see (one probe over the compiled modules of the batch).
  6. Green: the batch is verified. Red: `triage` maps every failure to the deliveries of the batch that wrote the
     failing module or changed a module it imports. A failure with one possible cause is decided here; more than three suspects go to
     an independent Codex agent on the groups' machine (local/batch/triage/<batch>-r<n>/request.md -> verdict.json),
     which says for each failure whether the delivered module is wrong, or correct and broken by another delivery of
     the batch. The deliveries at fault are taken out (tools/landing.py revert, their records put back) and returned
     with the compiler's message and the reason; the build runs again. Suspects and their batch dependents are removed together, then survivors are rebuilt, at most four rounds.
     No suspects or the round limit: ALERT and defer the failing import closures; never bisect.
     Repeated red source trees are never compiled again; unresolved states write ~/cc1/ALERT.

Usage (maintainer; SHEAF_LEAD=L-only):
  tools/batch_land.py step                      one step of the cycle (~/cc1/autoland3.py calls this in a loop)
  tools/batch_land.py status                    the open batch, the passed deliveries waiting
  tools/batch_land.py pass <G> <module> --head SHA --reviewer ID [--spot-checked NOTE] [--verdict PASS|FIX]
                                                record a reader's pass (what merge_delivery.py --stage 3 does)
  tools/batch_land.py take-out <G> <module> REASON   take a landed delivery of the open batch out and return it
"""
from __future__ import annotations
import calendar, json, os, pathlib, pickle, re, shutil, subprocess, sys, tempfile, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import merge_delivery as md  # noqa: E402
import leanindex as li  # noqa: E402
import landing as ld  # noqa: E402
import stage2_delivery as s2  # noqa: E402
import stage3_delivery as s3  # noqa: E402
import review_class as rc  # noqa: E402
import sorry_ledger as sl  # noqa: E402
import batch_recovery as recovery
import import_cycles as cycles
import repair_queue as repairs
from pipeline_guard import alert, clear_alert
import red_rework  # noqa: E402
import merge_jobs as mj  # noqa: E402   2026-10-26: conflicts go to merge agents (tools/merge_jobs.py)
import stage2_batch as s2b  # noqa: E402   2026-10-25: stage 2 lands in the same batches
import quarantine_wait as qwait  # noqa: E402   2026-10-28: imports quarantined -> the delivery waits, not returned
PRUNE_TIMEOUT = int(os.environ.get("SHEAF_PRUNE_TIMEOUT", "120"))

ROOT = md.ROOT
BD = ROOT / "local" / "batch"
PASSED, OPEN, CLOSED, TRIAGE = BD / "passed", BD / "open.json", BD / "closed", BD / "triage"
# Pipelined landing (the human, 2026-10-21; switch SHEAF_PIPELINE_BATCHES=1 in coord/sheaf.env, default off): while the
# global build of the open batch N runs, the next batch N+1 lands on top (local/batch/next.json), so that the next build
# verifies it. N+1 lands only when the running build contains every landing of N still open and an interface landing
# (so build.py does not start over for N+1), and N is not in recovery. When N closes, N+1 becomes the open batch. A red
# build that N must handle while N+1 exists first folds N+1 into N (one open batch again): the triage then sees exactly
# the landings the red build contained (last.json `included`), and a take-out of N carries along, fully undone, the
# landings of N+1 that changed the same files after it. No new batch lands while the open one is in recovery.
NEXT = BD / "next.json"
CLONE = ld.LOCAL / "buildtree"
STOP_REQUESTED = lambda: False


def MQ_LOG_FN(*a) -> None:
    MQ_LOG(" ".join(str(x) for x in a))


def MQ_LOG(line: str) -> None:
    """One line per merge-queue decision, in the lander's log (~/cc1/autoland.log when it runs)."""
    try:
        with open(os.environ.get("AUTOLAND_LOG") or pathlib.Path.home() / "cc1" / "autoland.log", "a") as f:
            f.write(time.strftime("%F %T ") + "merge queue: " + line + "\n")
    except OSError:
        pass


def stop_checkpoint():
    if STOP_REQUESTED(): raise Wait("stop requested between operations")


ROUNDS = 4
POOL = int(os.environ.get("SHEAF_BATCH_POOL", "4"))
# 2026-10-18: one step waited for the checks of ALL candidates (459 after the queue was widened, minutes each) before
# anything landed. Now a batch takes what is checked when no further check has finished for SHEAF_BATCH_QUIET seconds,
# at most SHEAF_BATCH_MAX deliveries (the global build and a triage of a red build stay tractable), after at most
# SHEAF_BATCH_MAX_WAIT seconds; the other checks go on in the pool and a later batch takes them.
QUIET = float(os.environ.get("SHEAF_BATCH_QUIET", "30"))
MAX_WAIT = float(os.environ.get("SHEAF_BATCH_MAX_WAIT", "900"))
BATCH_MAX = int(os.environ.get("SHEAF_BATCH_MAX", "150"))
# the human, 2026-10-20: landing is always batched, never one delivery at a time while others wait: a batch is
# everything checked and available. 2026-10-21 (the human): no idle wait for a minimum count; as soon as the previous
# batch is closed, ALL checked deliveries land as the next batch (one is fine when nothing else is waiting).
INDEX_SAVE = BD / "library-index.pkl"      # the library index of the prune check, kept across restarts (tip + index)
TRIAGE_WAIT = float(os.environ.get("SHEAF_TRIAGE_WAIT", "1500"))     # seconds for the Codex agent's verdict
NOTE_AUTO = ("AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the "
             "group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by "
             "a reviewer (stage 3, decision of the human 2026-10-12)")


class Refuse(Exception):
    """The delivery goes back to its group with this message."""


class Wait(Exception):
    """The delivery stays for a later cycle."""


def key(e) -> str:
    return f"{e['group']}/{e['item']}"


def read_json(p):
    try:
        return json.loads(pathlib.Path(p).read_text())
    except (OSError, ValueError):
        return None


def write_json(p, d):
    p = pathlib.Path(p); p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + ".tmp"); tmp.write_text(json.dumps(d, ensure_ascii=False, indent=1)); os.replace(tmp, p)


def marker(g, item) -> pathlib.Path:
    return PASSED / f"{g}__{item}.json"


# ---------------------------------------------------------------- a reader's pass

def cmd_pass(o) -> int:
    """tools/merge_delivery.py <G> <module> --stage 3: the static checks now, the landing by the next batch."""
    g, item = o.group, o.item
    br = md.branch_of(g, item)
    if not o.head:
        raise md.Fail("--stage 3 needs --head SHA (the commit the reviewer read)")
    if not md.has_ref(f"refs/heads/{br}"):
        raise md.Fail(f"no branch {br}")
    head = md.git("rev-parse", br)
    if not head.startswith(o.head):
        raise md.Fail(f"the branch head is {head[:9]}, not {o.head}: review the new head")
    over = {}
    if o.apply_fixes:
        over = fixes(pathlib.Path(o.apply_fixes).resolve(), g, item, head)
    c = {"group": g, "item": item, "head": head, "reviewer": o.reviewer, "overrides": over}
    try:
        plan = check(c, classify=False, merge_wait=False)
    except (Refuse, Wait) as e:
        raise md.Fail(str(e))
    if o.dry_run:
        print(f"DRY RUN {item} (stage 3): the static checks pass; {len(plan['D']['modules'])} module(s); nothing changed")
        return 0
    verdict = (o.verdict or ("FIX" if over else "PASS")).upper()
    write_json(marker(g, item), {"group": g, "item": item, "head": head, "reviewer": o.reviewer, "verdict": verdict,
                                 "note": o.spot_checked, "overrides": over, "time": ld.now()})
    print(f"QUEUED {item} {head[:9]}: passed by {o.reviewer}; the next batch lands it (tools/batch_land.py)")
    return 0


def fixes(fixdir: pathlib.Path, g, item, head) -> dict:
    base = md.git("merge-base", md.MAIN, head)
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item)
    by = {pathlib.PurePosixPath(m["file"]).name: m["file"] for m in D["modules"]}
    by.update({f"{n}.json": x["path"] for n, x in D["nodes"].items()})
    by.update({pathlib.PurePosixPath(p).stem + ".change.md": p for p in D["changes"]})
    by[f"{item}.report.md"] = D["report_path"]
    over = {}
    for fp in sorted(fixdir.iterdir()):
        if fp.name not in by:
            raise md.Fail(f"--apply-fixes: {fp.name} is not a file of the delivery")
        over[by[fp.name]] = fp.read_text()
    return over


# ---------------------------------------------------------------- the checks, without a lock

def returned_head(g, head) -> bool:
    p = ROOT / "coord" / "returns" / f"{g}.md"
    try:
        return head[:9] in p.read_text()
    except OSError:
        return False


def candidates(cache: dict) -> list[dict]:
    """The deliveries a batch may take: passed by a reader (marker with the branch's head), or of class AUTO."""
    out = []
    live = set()
    heads = set()
    try:
        qwaits, qrows = qwait.load(), qwait.rework.load()
    except Exception:  # noqa: BLE001
        qwaits, qrows = {}, {}
    for g, item in rc.branches():
        if not s3.is_stage3_item(item):
            continue
        head = rc.git("rev-parse", f"deliver/{g}/{item}").strip()
        if not head:
            continue
        live.add(marker(g, item).name)
        try:
            who = json.loads((ROOT / "coord" / "claims" / f"{item}.lock").read_text()).get("who")
        except (OSError, ValueError):
            who = None
        if who != g:
            # 2026-10-21: a delivery branch whose group no longer holds the claim (released, taken out, handed off) made
            # the dispatcher count the item as taken, so nobody worked it again (21 items, 3 h): kept under refs/orphaned/
            br = f"refs/heads/deliver/{g}/{item}"
            if subprocess.run(["git", "update-ref", "refs/orphaned/deliver/" + g + "/" + item, br], cwd=ROOT).returncode == 0:
                subprocess.run(["git", "update-ref", "-d", br, head], cwd=ROOT)
            continue
        if g.startswith('XR'):
            job = repairs.read(repairs.JOBS / (g[2:] + '.json'))
            if job.get('state') != 'delivered' or job.get('repaired_head') != head:
                continue  # dedicated reader/result has not accepted this exact repair
        if returned_head(g, head):
            continue        # this head was returned; the group pushes a new one
        heads.add(head)
        if qwaits and qwait.holding(head, qwaits, qrows):
            continue        # 2026-10-28: an import is still quarantined (tools/quarantine_wait.py); not checked again yet
        mk = read_json(marker(g, item))
        if mk and mk.get("head") == head:
            if mk.get("not_before", 0) > time.time(): continue
            out.append({"group": g, "item": item, "head": head, "reviewer": mk["reviewer"], "note": mk.get("note"),
                        "verdict": mk.get("verdict") or "PASS", "overrides": mk.get("overrides") or {}, "passed": True})
            continue
        if mk:
            marker(g, item).unlink(missing_ok=True)     # the branch moved after the pass: the new head is classified
        if cache.get(head, "AUTO") != "AUTO":
            continue
        out.append({"group": g, "item": item, "head": head, "reviewer": None, "note": NOTE_AUTO, "verdict": "PASS",
                    "overrides": {}, "passed": False})
    if qwaits:
        try:
            qwait.prune(heads)
        except Exception:  # noqa: BLE001
            pass
    if PASSED.is_dir():
        for p in PASSED.glob("*.json"):
            if p.name not in live:
                p.unlink(missing_ok=True)               # the branch is gone
    out.sort(key=lambda c: (not bool((read_json(marker(c["group"], c["item"])) or {}).get("repair_priority")), c["group"], c["item"]))
    return freeze_filter(out)


FROZEN: dict = {}


def freeze_filter(cands: list[dict]) -> list[dict]:
    """2026-10-28 (the human, 02:50 CST): while more than SHEAF_FREEZE_BLOCKED (100) modules are blocked (tools/freeze.py,
    local/batch/freeze.json) only rework fixes land with the cluster restores; every other delivery waits on its branch,
    not checked and not returned. FROZEN describes the last filtering (land_batch logs it)."""
    import freeze
    st = freeze.state()
    if not st.get("frozen"):
        FROZEN.clear()
        return cands
    keep, wait = freeze.split(cands)
    FROZEN.clear()
    FROZEN.update(blocked=st.get("blocked"), limit=st.get("limit") or freeze.limit(), wait=len(wait), keep=len(keep))
    return keep


def inflight_files() -> set[str]:
    return {"lean/" + f["path"] for r in ld.records(ld.INFLIGHT) for f in r["files"]}


def index_module(text: str) -> dict:
    """What tools/import_prune_check.py reads of a library module (li.scan, li.library_statements): its imports,
    its declared names and its theorem statements (only those long enough to be compared, see new_stmts there)."""
    out = {"imports": set(), "decls": set(), "stmts": {}}
    try:
        out["imports"] = li.imports_of(text)
        out["decls"] = li.decls_in_text(text)
        out["stmts"] = {q: s for q, s in li.statements_in_text(text).items() if s and len(s) >= 40}
    except li.LexError:
        pass        # a text the lexer refuses declares nothing for the check; the global build reads it
    return out


def library_module(mod: str) -> bool:
    return mod.split(".")[0] in li.library_dirs() or mod in ("Challenge", "TargetsCheck")


def library_index() -> dict:
    """index_module of every module li.library_files() lists, from the working tree (what the scanners read)."""
    out = {}
    for p in li.library_files():
        try:
            text = p.read_text(errors="ignore")
        except FileNotFoundError:
            continue
        out[li.module_of(p)] = index_module(text)
    return out


# Runs in the check process for one module: with an index file, li.scan and li.library_statements answer from the
# lander's index of the library at its tip (plus the delivery's modules) and li.file_of reads the delivery's files
# from the overlay; without one (a reader's pass), the old way: a symlink copy of the whole library is scanned.
PRUNE_WORKER = r"""
import sys, pathlib, pickle, collections
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, sys.argv[2]); import leanindex as li
ov, index_file = pathlib.Path(sys.argv[3]), sys.argv[4]
if not index_file:
    li.LEAN = ov
else:
    from batch_land import index_module
    with open(index_file, "rb") as f: index = pickle.load(f)
    for p in ov.rglob("*.lean"):
        index[".".join(p.relative_to(ov).with_suffix("").parts)] = index_module(p.read_text(errors="ignore"))
    real_file_of = li.file_of
    def file_of(mod):
        p = ov / pathlib.Path(*mod.split(".")).with_suffix(".lean")
        return p if p.is_file() else real_file_of(mod)
    def scan():
        decls, imports = collections.defaultdict(set), {}
        for mod, x in index.items():
            if mod != "Challenge":
                for q in x["decls"]: decls[q].add(mod)
            imports[mod] = set(x["imports"])
        return decls, imports
    def library_statements():
        out = collections.defaultdict(set)
        for mod, x in index.items():
            if mod in ("Challenge", "TargetsCheck"): continue
            for q, s in x["stmts"].items(): out[s].add((q, mod))
        return out
    li.file_of, li.scan, li.library_statements = file_of, scan, library_statements
import import_prune_check as c
sys.argv = ["import_prune_check.py"] + sys.argv[5:]; sys.exit(c.main())
"""


def prune_check(D: dict, index_file: str | None = None) -> str | None:
    """tools/import_prune_check.py for every module, against the library with the delivery's files in place (what
    land.sh and land_set.sh check after writing). None, or the findings. `index_file`: the lander's library index
    (Pre.snapshot); without it every module's check scans the whole library (16 000 files: minutes, 2026-10-18)."""
    if os.environ.get("SHEAF_SKIP_PRUNE") == "1":
        # the human, 2026-10-13 17:55 +08: land the waiting deliveries at once and let the global build judge;
        # what breaks it is taken out and repaired (repair_queue) - faster than a per-delivery library scan
        return None
    with tempfile.TemporaryDirectory(prefix="sheaf-batch-") as td:
        td = pathlib.Path(td); ov = td / "lean"; ov.mkdir()
        if not index_file:
            src = [str(li.LEAN / d) for d in li.library_dirs() if (li.LEAN / d).is_dir()] + [str(p) for p in li.LEAN.glob("*.lean")]
            subprocess.run(["cp", "-as", *src, str(ov)], check=True, capture_output=True)
        for m in D["modules"]:
            p = ov / m["file"][len("lean/"):]
            p.parent.mkdir(parents=True, exist_ok=True)
            if p.is_symlink() or p.exists():
                p.unlink()
            p.write_text(m["text"])
        for m in D["modules"]:
            old = td / "old.lean"
            if m["old"] is None:
                oldp = "/dev/null"
            else:
                old.write_text(m["old"]); oldp = str(old)
            # 2026-10-24: at most PRUNE_TIMEOUT s per module. A delivery that removed ~40 imports kept this textual check
            # busy for 3.5 h and held the delivery out of every batch; past the limit the global build decides (a
            # module it breaks goes back to its writer or becomes a rework item, tools/batch_land.py mechanical_red)
            try:
                r = subprocess.run([sys.executable, "-c", PRUNE_WORKER, str(ROOT / "tools"), str(pathlib.Path(__file__).resolve().parent), str(ov), index_file or "",
                                    m["module"], oldp, str(ov / m["file"][len("lean/"):])], cwd=ROOT, capture_output=True, text=True,
                                   timeout=PRUNE_TIMEOUT)
            except subprocess.TimeoutExpired:
                continue
            if r.returncode != 0:
                return f"refused by tools/import_prune_check.py for {m['file']}: " + " | ".join(
                    (r.stdout + r.stderr).strip().splitlines()[-25:])
    return None


IMPORT_LINE = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)\s*$")


def imports_added(old: str | None, now: str | None) -> list[str] | None:
    """The import lines `now` has and `old` lacks, when that is their only difference; None otherwise."""
    if old is None or now is None or old == now:
        return None
    ol = old.split("\n")
    have = {l.strip() for l in ol}
    added, rest = [], []
    for l in now.split("\n"):
        (added if IMPORT_LINE.match(l) and l.strip() not in have else rest).append(l)
    return added if added and rest == ol else None


def merge_imports(text: str, added: list[str]) -> str:
    """`text` with the import lines `added` that it lacks, after its last import (after `module` if it has none)."""
    L = text.split("\n")
    mods = {IMPORT_LINE.match(l).group(1) for l in L if IMPORT_LINE.match(l)}
    add = [l for l in added if IMPORT_LINE.match(l).group(1) not in mods]
    ks = [i for i, l in enumerate(L) if IMPORT_LINE.match(l)] or [i for i, l in enumerate(L) if l.strip() == "module"]
    k = ks[-1] + 1 if ks else 0
    return "\n".join(L[:k] + add + L[k:])


def writers_since(base: str, path: str) -> str:
    """the commits on the main branch since `base` that touched `path` (short), for the return message"""
    out = md.git("log", "--format=%h %s", f"{base}..{md.MAIN}", "--", path, check=False).splitlines()
    return "; ".join(l[:90] for l in out[:3]) + (f"; {len(out) - 3} more" if len(out) > 3 else "") if out else "uncommitted change"


def check(c: dict, classify: bool = True, merge_wait: bool = True) -> dict:
    """Every check that needs no lock. Returns the plan of the landing; Refuse or Wait otherwise. A file changed on the
    main branch since the delivery's base is merged by a merge agent (tools/merge_jobs.py): Wait until its job is done
    (merge_wait=False, a reader's pass: the job is requested and the checks go on with the delivery's own text)."""
    g, item, head = c["group"], c["item"], c["head"]
    reviewer = c.get("reviewer")
    base = md.git("merge-base", md.MAIN, head)
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item, overrides=c.get("overrides") or None)
    if classify and not c.get("passed"):
        cl, why, h = rc.classify(g, item, D)
        if h != head:
            raise Wait("the branch moved during the checks")
        if cl != "AUTO":
            raise Wait(f"class {cl}: {why[:200]}")       # a reader's; not this tool's
        reviewer = "COMPILER" if why.startswith("compiler-only") else "AUTO"
    if time.time() - int(md.git("show", "-s", "--format=%ct", base)) > md.MAX_AGE:
        raise Refuse(f"base {base[:7]} is too far behind {md.MAIN}: pull, rebase, push again")
    if D["fails"]:
        raise Refuse("; ".join(f"({L}) {x}" for L, x in D["fails"][:6]))
    # stage3_delivery already refuses ordinary definition holes and new forbidden
    # keyword kinds. Supplement only its admit, quoted-name and data-field gaps.
    for module in D["modules"]:
        if module["text"] is None:
            continue
        missing = sl.missing_gate(module["old"], module["text"])
        if missing:
            raise Refuse(module["file"] + ": " + "; ".join(missing[:6]))
    why3 = s3.classify(D, g, item)
    if reviewer == "AUTO" and why3:
        raise Refuse("not AUTO: " + "; ".join(why3))
    subject = md.git("show", "-s", "--format=%s", head)
    if subject != f"Prove {item} ({g})":
        raise Refuse(f"the commit of the delivery is `{subject[:80]}`, not `Prove {item} ({g})`: nothing shows that the "
                     "group's delivery tool compiled its modules with the probe, and the server does not compile a "
                     "delivery again; deliver with the delivery tool")
    busy = inflight_files()
    cur, write, merged_any, conflicts = {}, [], False, []
    base_texts = {m["file"]: s2.Git(ROOT).show(base, m["file"]) for m in D["modules"]}
    for m in D["modules"]:
        p = ROOT / m["file"]
        now = p.read_text() if p.is_file() else None
        cur[m["file"]] = now
        if now == m["text"]:
            continue
        if m["file"] in busy:
            raise Wait(f"{m['file']} is in a landing that is still being checked")
        # 2026-10-20: compare with the library's file at the delivery's base, not with m["old"]: for a rework restore
        # m["old"] is the quarantined text while the library has no file at all, so every restore used to be refused
        base_text = base_texts[m["file"]]
        if now == base_text:
            write.append(m["file"]); continue
        added = imports_added(base_text, now)
        if added is not None and m["text"] is not None:
            # the library's file differs from the delivery's base only by added import lines (the proof imports written
            # into the modules on 2026-10-12, tools/add_proof_imports.py): the delivery keeps its content and gets them
            m["text"] = merge_imports(m["text"], added)
            if m["old"] == base_text:
                m["old"] = now
            D["notes"].append(f"{m['file']}: {len(added)} import line(s) added on {md.MAIN} since the base were merged in")
            merged_any = True
            if now == m["text"]:
                continue
            write.append(m["file"]); continue
        if now is None or m["text"] is None:
            by = writers_since(base, m["file"])
            gone = now is None and base_text is not None
            raise Refuse(f"{m['file']} " + ("was removed from lean/ on " if gone else "was created on " if base_text is None
                         else "changed on ") + f"{md.MAIN} after the delivery's base {base[:9]} (by {by})"
                         + (": the module is quarantined now (coord/rework.tsv); claim its rework item and restore it from "
                            "quarantine/" if gone else ": take the file as it is now, make your change in it, compile and "
                            "deliver again"))
        # 2026-10-26 (the human): no text merge (git merge-file joined characters, not intents: 14.9 % of such landings
        # reverted against 2.0 %). The file goes to a merge agent; the delivery waits for its job (tools/merge_jobs.py)
        conflicts.append({"file": m["file"], "base": base_text or "", "target": now, "ours": m["text"]})
    # 2026-10-26 evening (the human): DAG node conflicts go to the merge agent too, not back to the worker: a node the
    # delivery creates that exists on main now, or a node field both the delivery and main changed differently
    for nid, x in D["nodes"].items():
        p = ROOT / x["path"]
        cur_t = p.read_text() if p.is_file() else None
        if cur_t is None:
            continue
        ours_t = mj.dump(x["node"])
        if x["role"] == "new":
            conflicts.append({"file": x["path"], "base": "", "target": cur_t, "ours": ours_t}); continue
        try:
            cur_n = json.loads(cur_t)
        except ValueError:
            continue
        b = x["base_node"] or {}
        if any(b.get(f) != x["node"].get(f) and cur_n.get(f) != b.get(f) and cur_n.get(f) != x["node"].get(f)
               for f in s3.STAGE3_OWNS + s3.STAGE3_STATEMENT + s3.STAGE3_PRUNES):
            conflicts.append({"file": x["path"], "base": s2.Git(ROOT).show(base, x["path"]) or "", "target": cur_t, "ours": ours_t})
    if conflicts:
        st, got = mj.resolve(g, item, head, base, conflicts, mj.delivery_files(D), D.get("report"))
        if st == "failed":
            raise Refuse(got)
        if st == "wait" and merge_wait:
            raise Wait(got)
        for m in D["modules"]:
            if st != "merged" or m["file"] not in got:
                if st == "wait" and any(x["file"] == m["file"] for x in conflicts):
                    write.append(m["file"])         # a reader's pass: checked with its own text; the batch waits for the job
                continue
            now, base_text = cur[m["file"]], base_texts[m["file"]]
            m["text"] = got[m["file"]]
            if m["old"] == base_text:
                m["old"] = now
            m["diff"] = s3.diff_module(m["old"], m["text"])
            D["notes"].append(f"{m['file']}: " + (f"changes on {md.MAIN} since the base ({writers_since(base, m['file'])}) merged by "
                              "a merge agent" if any(x["file"] == m["file"] for x in conflicts) else "changed by the merge agent")
                              + " (tools/merge_jobs.py), compiled alone with its importers")
            merged_any = True
            if now != m["text"] and m["file"] not in write:
                write.append(m["file"])
        if st == "merged":
            for nid, x in D["nodes"].items():
                if x["path"] not in got:
                    continue
                node = json.loads(got[x["path"]])
                if any(c["file"] == x["path"] for c in conflicts):
                    # lands as a change of main's node (land_one writes the fields that differ from it)
                    cur_t = (ROOT / x["path"]).read_text()
                    x.update(node=node, base_node=json.loads(cur_t), role="changed", merged_against=mj.sha(cur_t))
                else:
                    x["node"] = node
                D["notes"].append(f"{x['path']}: node merged by a merge agent (tools/merge_jobs.py; check_nodes passed)")
                merged_any = True
    if merged_any:
        for module in D["modules"]:
            if module["text"] is None:
                continue
            missing = sl.missing_gate(module["old"], module["text"])
            if missing:
                raise Refuse(module["file"] + " (after merging the library's changes): " + "; ".join(missing[:6]))
        why3 = s3.classify(D, g, item)
        if reviewer == "AUTO" and why3:
            raise Refuse("not AUTO after merging the library's changes: " + "; ".join(why3))
    if not write:
        raise Refuse("every module of the delivery is in the library already, with the same text")
    if reviewer == "AUTO":
        m0 = D["modules"][0]
        ch = li.interface_changes(m0["old"] or "", m0["text"] or "") if m0["old"] else ["(new module)"]
        # 2026-10-20: modules a rework cluster delivery restores verbatim or with proof changes only stay AUTO
        others = [m for m in D["modules"][1:] if not (m.get("role") == "restored"
                  and set(li.interface_changes(m["old"] or "", m["text"] or "")) <= {"(imports removed)"})]
        if others or (ch and not set(ch) <= {"(imports removed)"}):
            raise Refuse("the landing would be of kind interface, not proof: the delivery is CODEX")
    graph_file = c.get("_import_graph_file")
    if graph_file:
        with open(graph_file, "rb") as f:
            import_graph = pickle.load(f)
    else:
        import_graph = cycles.graph(li.LEAN)
    texts = {m["module"]: m["text"] for m in D["modules"]}
    try:
        cycles.refuse_missing(texts, cycles.source_modules(ROOT, pathlib.Path(graph_file).name.split("-imports")[0] if graph_file else "HEAD"), cycles.source_roots(ROOT))
    except RuntimeError as exc:
        w = qwait.wait(exc, g, item, head)
        if w:
            raise Wait(w) from exc
        raise Refuse(str(exc)) from exc
    cycle = cycles.closing_cycle(import_graph, texts)
    if cycle: raise Refuse("import cycle: " + " -> ".join(cycle))
    bad = prune_check(D, c.get("_library_index_file"))
    if bad:
        raise Refuse(bad)
    paths = {m["file"] for m in D["modules"]} | {x["path"] for x in D["nodes"].values()} | set(D["changes"]) | {D["report_path"]}
    # 2026-10-27 (the human): a landing that fixes a quarantined rework root (restore_after_fix then puts its importers
    # back) is checked first: not the failing quarantined text again, and the root compiles alone against the live build
    # (tools/rework_fixcheck.py; Refuse: back to the writer with the error; Wait: an import has no .olean yet)
    import rework_fixcheck as rfc
    rootfix = rfc.verify(D, item, head, Refuse, Wait, compile=merge_wait)   # a reader's pass: the batch compiles it
    if rootfix:
        D["notes"].append("rework root fix checked before the cluster restore: "
                          + ", ".join(f"{m} {s}" for m, s in rootfix.items()))
    return dict(c, reviewer=reviewer, base=base, D=D, cur=cur, write=write, paths=sorted(paths), rootfix=rootfix)


def importer_recheck(plan: dict) -> None:
    """2026-10-27 (the human): a reader-passed delivery that changes the interface of existing modules has the direct
    importers of those modules compiled again before it lands, those whose source changed since the review packet's
    compile (tools/importer_compile.py recheck: changed, new, sorry stub then, or not OK then). One that now fails with the
    delivery and compiles on main without it refuses the landing (Refuse: back to the writer with the compiler message).
    Pre-existing failures, INFRA, SLOW and a failure of the recheck itself do not refuse; importers not compiled yet
    (busy slots) make it wait, at most SHEAF_S3_RECHECK_WAIT seconds. Called after check() by
    _check, outside it (check() and the merge-agent path are maintained separately).
    2026-10-27 (three red builds in one evening, ~3100 importers quarantined, all from "(interface, COMPILER)" landings
    that broke a direct importer): an AUTO/COMPILER delivery (no reader, no packet compile) gets the same recheck when
    it changes the interface of an existing module that has importers outside the delivery (importer_compile.plan:
    every direct importer compiled, there is no review evidence); a proof-only one is not compiled, as before."""
    auto = plan.get("reviewer") in ("AUTO", "COMPILER")
    if not plan.get("passed") and not auto:
        return
    try:
        import importer_compile as ic
        # 2026-10-27 22:40 (the owner): the related set (direct importers and the transitive importers that mention a
        # changed name or an affected class: importer_compile.related_plan), not only the direct importers
        if auto and not ic.related_plan(plan["D"])["compile"]:
            return
        r = ic.recheck(plan["D"], plan["head"])
    except Exception as e:  # noqa: BLE001   the global build still verifies the landing
        try:
            with open(ROOT / "local" / "importer-checks" / "recheck-errors.log", "a") as f:
                f.write(f"{time.strftime('%F %T')} {plan['group']} {plan['item']} {plan['head'][:9]} {e!r}"[:600] + "\n")
        except OSError:
            pass
        return
    if r["compiled"]:
        plan["D"].setdefault("notes", []).append(
            f"importer recheck at landing: {len(r['compiled'])} related module(s) compiled again"
            + (f" ({len(r['worker_reused'])} reused from the worker's compile)" if r.get("worker_reused") else "")
            + (f", pre-existing failures {', '.join(r['pre_existing'])}" if r["pre_existing"] else "")
            + (f", not decided: {', '.join(f'{u} {s}' for u, s in r['other'].items())}" if r["other"] else "")
            + (f", not compiled: {len(r['not_run'])}" if r["not_run"] else ""))
    if r["new_fail"]:
        msg = "; ".join(f"importer {u} now fails against this delivery ({r['compiled'].get(u, '')}; it compiles on "
                        f"{md.MAIN} without the delivery):\n{out.strip()[-1200:]}" for u, out in r["new_fail"].items())
        raise Refuse("the importer recheck at landing (tools/importer_compile.py recheck): " + msg[:2800]
                     + "\nAdapt the delivery so that the importer compiles (changes inside the delivery's own files), "
                     "compile it with the importer, deliver again.")
    wait_max = float(os.environ.get("SHEAF_S3_RECHECK_WAIT", "10800"))
    if r["not_run"] and time.time() - r["first"] < wait_max:
        # busy compile slots: the delivery waits for the next step, which compiles the rest (results are kept); after
        # SHEAF_S3_RECHECK_WAIT (3 h) of waiting it lands and the global build decides
        raise Wait(f"importer recheck: {len(r['not_run'])} of {len(r['compiled'])} related module(s) not compiled yet "
                   f"(compile slots busy), e.g. {', '.join(r['not_run'][:3])}")


def _check(c):
    try:
        plan = check(c)
        importer_recheck(plan)
        return "ok", plan
    except Refuse as e:
        return "refuse", str(e)
    except Wait as e:
        return "wait", str(e)
    except Exception as e:  # noqa: BLE001   a delivery the tools cannot read stays for a reader
        return "error", repr(e)[:300]


class Pre:
    """The checks, POOL deliveries at a time, each in a process of its own (tools/queue.py hides the standard module
    `queue`, so neither multiprocessing nor concurrent.futures can be imported from tools/). The loop calls pump()
    while a batch waits for its build, so the next batch is checked by the time it may land; a result is kept by the
    head it was computed for, and the landing compares the head and the library files with it again under the lock."""

    def __init__(self):
        self.dir = pathlib.Path(tempfile.mkdtemp(prefix="sheaf-batch-"))
        self.running, self.done = {}, {}
        self.import_graph, self.graph_tip, self.graph_file = None, None, None
        self.index, self.index_tip, self.index_file, self.index_saved = None, None, None, 0.0

    @staticmethod
    def changed(a: str, b: str) -> dict:
        """module -> text at `b` (None: removed) for the lean/ files that differ between the commits `a` and `b`."""
        texts = {}
        for path in md.git('diff', '--name-only', a, b, '--', 'lean/').splitlines():
            if path.endswith('.lean'):
                data = recovery.blob(ROOT, b, path)
                texts[path[5:-5].replace('/', '.')] = data.decode(errors='ignore') if data is not None else None
        return texts

    def snapshot(self):
        """One graph scan, then update only modules changed at an external tip."""
        tip = md.git('rev-parse', 'HEAD')
        if self.import_graph is None:
            self.import_graph = cycles.graph(li.LEAN)
        elif tip != self.graph_tip:
            self.import_graph = cycles.overlay(self.import_graph, self.changed(self.graph_tip, tip))
        if tip != self.graph_tip or self.graph_file is None:
            self.graph_file = self.dir / (tip + '-imports.pkl')
            with self.graph_file.open('wb') as f: pickle.dump(self.import_graph, f, protocol=pickle.HIGHEST_PROTOCOL)
            self.graph_tip = tip
        self.snapshot_index(tip)
        for p in self.dir.glob('*.pkl'):                 # the graphs and indexes of older tips, once no check reads them
            if p.name.endswith(('-imports.pkl', '-index.pkl')) and p not in (self.graph_file, self.index_file) \
                    and time.time() - p.stat().st_mtime > 3600:
                p.unlink(missing_ok=True)
        return self.import_graph

    def snapshot_index(self, tip: str) -> None:
        """The library index of the prune check (index_module per module) at `tip`: built once from the working tree
        or taken from INDEX_SAVE, then updated for the modules changed between tips, written per tip for the check
        processes (2026-10-18: before, every check scanned the 16 000 files of the library itself, minutes each)."""
        if os.environ.get("SHEAF_SKIP_PRUNE") == "1":
            return
        if self.index is None:
            if not self.load_index(tip):
                self.index, self.index_tip = library_index(), tip
            self.save_index(force=True)
        elif tip != self.index_tip:
            self.update_index(self.changed(self.index_tip, tip))
            self.index_tip = tip
        want = self.dir / (tip + '-index.pkl')
        if self.index_file != want or not want.exists():
            tmp = want.with_suffix('.tmp')
            with tmp.open('wb') as f: pickle.dump(self.index, f, protocol=pickle.HIGHEST_PROTOCOL)
            os.replace(tmp, want); self.index_file = want
            self.save_index()

    def update_index(self, texts: dict) -> None:
        for mod, text in texts.items():
            if text is None or not library_module(mod): self.index.pop(mod, None)
            else: self.index[mod] = index_module(text)

    def load_index(self, tip: str) -> bool:
        """INDEX_SAVE brought to `tip`; False when there is none or its tip is not a commit of this repository."""
        try:
            with INDEX_SAVE.open('rb') as f: saved = pickle.load(f)
            if not (isinstance(saved, dict) and saved.get('version') == 1 and saved.get('tip') and isinstance(saved.get('index'), dict)):
                return False
            self.index, self.index_tip = saved['index'], saved['tip']
            if self.index_tip != tip:
                self.update_index(self.changed(self.index_tip, tip))
                self.index_tip = tip
            return True
        except Exception:  # noqa: BLE001
            self.index, self.index_tip = None, None
            return False

    def save_index(self, force: bool = False) -> None:
        if not force and time.time() - self.index_saved < 600:
            return
        try:
            tmp = INDEX_SAVE.with_suffix('.tmp'); INDEX_SAVE.parent.mkdir(parents=True, exist_ok=True)
            with tmp.open('wb') as f: pickle.dump({'version': 1, 'tip': self.index_tip, 'index': self.index}, f, protocol=pickle.HIGHEST_PROTOCOL)
            os.replace(tmp, INDEX_SAVE); self.index_saved = time.time()
        except OSError:
            pass

    def pump(self, cands: list[dict]) -> None:
        for h, (p, out) in list(self.running.items()):
            if p.poll() is None:
                continue
            del self.running[h]
            try:
                self.done[h] = pickle.loads(out.read_bytes())
            except Exception:  # noqa: BLE001
                self.done[h] = ("error", f"the check process ended with exit code {p.returncode}")
            out.unlink(missing_ok=True)
        if cands:
            self.snapshot()
            for c in cands:
                c['_import_graph_file'] = str(self.graph_file)
                c['_library_index_file'] = str(self.index_file) if self.index_file else None
        live = {c["head"] for c in cands}
        for h in [h for h in self.done if h not in live]:
            del self.done[h]
        for c in cands:
            h = c["head"]
            if len(self.running) >= POOL:
                break
            if h in self.done or h in self.running:
                continue
            out = self.dir / f"{h}.pkl"
            p = subprocess.Popen([sys.executable, str(pathlib.Path(__file__).resolve()), "check-one", str(out)], cwd=ROOT,
                                 stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            p.stdin.write(json.dumps(c).encode()); p.stdin.close()
            self.running[h] = (p, out)

    def results(self, cands: list[dict]) -> list[tuple]:
        """[(candidate, result)] for the candidates whose check is done: all of them, or those done when no check
        has finished for QUIET s, BATCH_MAX are done, or MAX_WAIT s have passed (the rest stay in the pool)."""
        t0, last, ndone = time.time(), None, 0
        while True:
            stop_checkpoint()
            self.pump(cands)
            done = [c for c in cands if c["head"] in self.done]
            if len(done) == len(cands):
                break
            if len(done) != ndone:
                ndone, last = len(done), time.time()
            if done and (time.time() - last >= QUIET or len(done) >= BATCH_MAX):
                break
            if time.time() - t0 >= MAX_WAIT:
                break
            time.sleep(0.2)
        return [(c, self.done[c["head"]]) for c in done]


# ---------------------------------------------------------------- the landing, under the lock

def land_one(plan: dict, batch_id: str) -> dict:
    """Write, register and commit one delivery. Called with coord/.merge.lock held."""
    if (BD / 'proof-imports.json').exists(): raise Wait('proof-import cycle is committing')
    g, item, head, D, reviewer = plan["group"], plan["item"], plan["head"], plan["D"], plan["reviewer"]
    br = md.branch_of(g, item)
    if not md.has_ref(f"refs/heads/{br}") or md.git("rev-parse", br) != head:
        raise Wait("the branch moved after the checks")
    for m in D["modules"]:
        p = ROOT / m["file"]
        if (p.read_text() if p.is_file() else None) != plan["cur"][m["file"]]:
            raise Wait(f"{m['file']} changed in the library after the checks")
    for nid, x in D["nodes"].items():
        if x.get("merged_against"):
            p = ROOT / x["path"]
            if mj.sha(p.read_text() if p.is_file() else None) != x["merged_against"]:
                raise Wait(f"the node {nid} changed on {md.MAIN} after its merge: checked again")
        elif x["role"] == "new" and (ROOT / x["path"]).exists():
            # 2026-10-26 evening (the human): not returned; the next check gives it to a merge agent
            raise Wait(f"the new node {nid} exists on {md.MAIN} now (another delivery created it): checked again, a merge agent merges it")
    # 2026-10-22 (the human): compare the lean/ tree, not HEAD: coord-only commits (queue, claims, bookkeeping) land every
    # minute and bounced deliveries for hours with "the library moved"
    if plan.get("cycle_tip_lean") and md.git("rev-parse", "HEAD:lean") != plan["cycle_tip_lean"]:
        raise Wait("the library moved after the import-cycle check; retry on the new tip")
    mods = D["modules"]
    rels = [f[len("lean/"):] for f in plan["write"]]
    # the human, 2026-10-20 (tools/rework.py): a rework item restores a quarantined module; its import lines go back into
    # the root files they were removed from, in this same landing (compiled by the build, taken out with it)
    import rework
    roots_add = {}
    for m in [item] + [m["module"] for m in mods if m.get("role") == "restored"]:   # a cluster: every restored module
        for rel, text in rework.roots_to_restore(m).items():
            f0 = li.LEAN / rel
            cur = roots_add.get(rel)
            roots_add[rel] = rework.add_import_line(cur, m) if cur is not None else text
    
    rels += [r for r in roots_add if r not in rels]
    is_set = len(mods) > 1 or bool(roots_add)
    r = subprocess.run([sys.executable, "tools/landing.py", "begin", "L", *rels], cwd=ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise Wait("landing.py begin: " + (r.stderr or r.stdout).strip()[:300])
    landing = r.stdout.strip().splitlines()[-1]
    tree, book, done = md.Tree(), {"group": g, "item": item}, False
    try:
        for m in mods:
            if m["file"] in plan["write"]:
                p = ROOT / m["file"]
                if m["text"] is None:      # a retired Sheaf copy (coord/retire-items.tsv)
                    p.unlink(missing_ok=True); continue
                p.parent.mkdir(parents=True, exist_ok=True); p.write_text(m["text"])
        for rel, text in roots_add.items():
            (li.LEAN / rel).write_text(text)
        r = subprocess.run([sys.executable, "tools/landing.py", "finish", landing] + (["--set"] if is_set else []),
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            raise md.Fail("landing.py finish: " + (r.stderr or r.stdout).strip()[:300])
        done = True
        kind = r.stdout.strip().splitlines()[-1]
        req = ld.REQUESTS / f"{landing}.json"
        rec = ld.read_json(req) or {}
        if reviewer == "AUTO" and kind != "proof" and set(rec.get("changed") or ["?"]) <= {"(imports removed)"}:
            kind = "proof"      # a removed public import in a module nobody imports: the one interface landing of AUTO
        allowed = {m["module"]: sorted(set(m["diff"]["sorry_before"]) - set(m["diff"]["body_changed"]) | set(m["diff"]["new_sorry"]))
                   for m in mods}
        rec.update(batch=batch_id, delivery={"group": g, "item": item, "head": head}, sorry_allowed=allowed)
        ld.write_json(req, rec)
        rv = {"date": md.today(), "by": "L", "reviewer": reviewer, "group": g, "result": plan["verdict"].lower(),
              "landing": landing, "kind": kind}
        if plan.get("note"):
            rv["note"] = plan["note"]
        paths = []
        for nid, x in D["nodes"].items():
            if x["role"] == "new":
                nd = dict(x["node"])
                nd["reviewed"] = dict(rv, note="new node of a stage-3 delivery, read against its source by the reviewer")
            else:
                nd = json.loads((ROOT / x["path"]).read_text())
                for k in s3.STAGE3_OWNS + s3.STAGE3_STATEMENT:   # only what the delivery changed against its base
                    if (x["base_node"] or {}).get(k) == x["node"].get(k):
                        continue
                    if k in x["node"]:
                        nd[k] = x["node"][k]
                    else:
                        nd.pop(k, None)
                s3.apply_tool_uses_pruning(nd, x["base_node"] or {}, x["node"])
            nd["reviewed_proof"] = rv
            tree.write(x["path"], md.dump(nd)); paths.append(x["path"])
        for p in plan["item_nodes"]:                             # the node(s) of the item's module
            if p in paths:
                continue
            nd = json.loads((ROOT / p).read_text())
            m0 = next(m for m in mods if m["role"] == "item")
            nd["reviewed_proof"] = dict(rv, sorry_before=m0["diff"]["sorry_before"], sorry_after=m0["diff"]["sorry_after"])
            tree.write(p, md.dump(nd)); paths.append(p)
        for p, t in D["changes"].items():
            t2 = re.sub(r"(?m)^(## Status\n+)open\b.*$", f"\\1landed {landing} {md.today()} (merge of {br})", t)
            tree.write(p, t2); paths.append(p)
        tree.write(D["report_path"], D["report"]); paths.append(D["report_path"])
        rp, rtext, parts = md.return_entries(g, item)
        keep = [x for x in parts if not x.startswith(f"## {item} (")]
        returned = rtext is not None and len(keep) != len(parts)
        book["returns"] = (rp, rtext)
        if returned:
            rp.write_text("".join(keep)); paths.append(rp.relative_to(ROOT).as_posix())
        claim = ROOT / "coord" / "claims" / (item.replace("/", "__") + ".lock")
        claim_text = claim.read_text() if claim.exists() else None
        book["claim"] = (claim, claim_text)
        dlog = ROOT / "coord" / "deliveries.log"
        book["dlog"] = (dlog, dlog.read_text() if dlog.exists() else "")
        subprocess.run([sys.executable, "tools/claim.py", "done", g, item,
                        f"delivered by {g} on {br}, merged by L (reviewer {reviewer})"], cwd=ROOT, capture_output=True)
        book["ledger"] = md.ledger_line(
            f"merged {br} (stage 3; reviewer {plan['verdict']}; {'after a return' if returned else 'first push'}; "
            f"landing {landing} ({kind}); batch {batch_id}; modules {len(mods)}; new nodes "
            f"{sum(1 for x in D['nodes'].values() if x['role'] == 'new')}"
            + (f"; change records: {', '.join(D['changes'])}" if D["changes"] else "") + ")")
        paths += [m["file"] for m in mods] + ["lean/" + rel for rel in roots_add] + ["coord/ledger.md", "coord/deliveries.log"]
        if claim_text is not None and md.exists_at("HEAD", claim.relative_to(ROOT).as_posix()):
            paths.append(claim.relative_to(ROOT).as_posix())
        author = md.git("show", "-s", "--format=%an <%ae>", D["commits"][-1]) if D["commits"] else "L"
        note = ROOT / "coord" / "repair-notes" / (item + ".json")
        if note.exists() and md.git("status", "--porcelain", "--", note.relative_to(ROOT).as_posix()).strip():
            paths.append(note.relative_to(ROOT).as_posix())
        md.git_retry("add", "-A", "--", *paths)
        md.git_retry("commit", "-q", f"--author={author}", "-m",
                     f"Prove {item} ({g}, reviewed by {reviewer})\n\nDelivered by group {g} ({br}); landing "
                     f"{landing} ({kind}); batch {batch_id}, which the global build verifies; merged by "
                     "tools/batch_land.py for L.", "--", *paths)
    except BaseException:
        tree.restore(); md.unbook(book)
        subprocess.run([sys.executable, "tools/landing.py", "revert" if done else "abort", landing]
                       + (["the batch landing did not commit"] if done else []), cwd=ROOT, capture_output=True)
        raise
    sha = md.git("rev-parse", "HEAD")
    md.git("branch", "-D", br, check=False)
    marker(g, item).unlink(missing_ok=True)
    if g.startswith('XR'):
        jp = repairs.JOBS / (g[2:] + '.json'); job = repairs.read(jp)
        if job:
            job['repair_landing'] = landing; repairs.write(jp, job)
    return {"group": g, "item": item, "head": head, "reviewer": reviewer, "landing": landing, "kind": kind,
            "commit": sha, "overrides": plan.get("overrides", {}), "modules": [m["module"] for m in mods], "claim": claim_text, "state": "landed"}


def land_batch(cache: dict, log, target: pathlib.Path | None = None) -> dict | None:
    """Steps 1-4. Returns the batch (also written to `target`: local/batch/open.json, or next.json when pipelined),
    or None when nothing landed."""
    target = target or OPEN
    if (BD / 'proof-imports.json').exists(): return None
    # 2026-10-21 (the human): putting quarantined modules back is a landing like any other, in the same batch: every
    # module no unfixed root blocks lands here with this batch; the batch's global build verifies it, the merge queue
    # takes out what fails (tools/rework.py settle_restores puts those back in quarantine)
    try:
        import rework
        rework.cluster_restore(wait=False)
    except Exception as exc:
        log("rework restore failed, the next batch tries again |", repr(exc)[:300])
    cands = candidates(cache)
    # 2026-10-25 (the human): stage-2 deliveries (reviewer-passed statements) land in the same batch and the same global
    # build; their own checks ran per delivery when the verdict was queued (tools/stage2_batch.py)
    pre2 = cache.setdefault("_pre2", s2b.Prep())
    try:
        s2ready = pre2.ready()     # checked by the pump at the start of every step
    except Exception as exc:  # noqa: BLE001
        log("stage 2: check pump failed |", repr(exc)[:300]); s2ready = []
    if FROZEN:
        note = (f"frozen: {FROZEN['blocked']} blocked > {FROZEN['limit']} (tools/freeze.py, ~/cc1/FREEZE): {FROZEN['wait']} "
                f"stage-3 and {len(s2ready)} stage-2 deliveries wait on their branches; {len(cands)} rework fix(es) may land")
        s2ready = []
        if cache.get("_freeze_note") != note or time.time() - cache.get("_freeze_note_t", 0) > 600:
            log(note); cache["_freeze_note"], cache["_freeze_note_t"] = note, time.time()
    if not cands and not s2ready:
        return None
    t0 = time.time()
    pre = cache.setdefault("_pre", Pre())
    # The source tree is fixed for this batch's checks. Scanning all library
    # files in every check worker costs about 16 seconds per delivery. Share
    # one snapshot with the workers; the in-process graph below is overlaid as
    # each delivery is accepted.
    import_graph = pre.snapshot()
    for c in cands:
        c['_import_graph_file'] = str(pre.graph_file)
        c['_library_index_file'] = str(pre.index_file) if pre.index_file else None
    pairs = pre.results(cands)
    pending_merge_jobs(pre, cands, log)
    pre.snapshot()
    base_modules = cycles.source_modules(ROOT, pre.graph_tip)
    package_roots = cycles.source_roots(li.LEAN)
    plans, taken, left, counts = [], {}, 0, {"refused": 0, "waiting": 0, "error": 0}
    for c, (st, x) in pairs:
        g, item, head = c["group"], c["item"], c["head"]
        if st == "ok":
            if len(plans) >= BATCH_MAX:
                left += 1; continue          # checked; the next batch takes it (its result stays in the pool)
            x = dict(x)
            clash = [p for p in x["paths"] if p in taken]
            if clash:
                log("waits for the next batch", g, item, head[:9], "|", f"{clash[0]} is written by {taken[clash[0]]} in this batch")
                continue
            texts = {m["module"]: m["text"] for m in x["D"]["modules"]}
            try:
                cycles.refuse_missing(texts, base_modules, package_roots)
            except RuntimeError as exc:
                pre.done.pop(head, None)
                w = qwait.wait(exc, g, item, head)
                if w:
                    log("not in this batch", g, item, head[:9], "|", w[:300]); continue
                give_back(g, item, head, str(exc), log)
                continue
            cycle = cycles.closing_cycle(import_graph, texts)
            if cycle:
                log("waits for the next batch", g, item, head[:9], "| import cycle:", " -> ".join(cycle))
                pre.done.pop(head, None)
                continue
            import_graph = cycles.overlay(import_graph, texts)
            for p in x["paths"]:
                taken[p] = key(c)
            plans.append(x)
        elif st == "refuse":
            pre.done.pop(head, None); counts["refused"] += 1
            give_back(g, item, head, x, log)
        elif st == "wait":
            pre.done.pop(head, None); counts["waiting"] += 1
            if x.startswith("class "):
                cache[head] = "READER"
            else:
                log("not in this batch", g, item, head[:9], "|", x[:300])
        else:
            pre.done.pop(head, None); counts["error"] += 1
            cache[head] = "ERROR"
            log("check error, left for a reader", g, item, head[:9], "|", x)
    if pairs: log(f"checks: {len(pairs)} of {len(cands)} candidates checked in {time.time() - t0:.0f} s; {len(plans)} to land, "
        f"{counts['refused']} refused, {counts['waiting']} waiting, {counts['error']} errors, {left} over the batch cap, "
        f"{len(cands) - len(pairs)} still being checked")
    # 2026-10-28 (red build 375085fafa: E5 added a hypothesis to NativeWeilTensorRingedChainData, K8's KFlatFlat proof,
    # importing it, landed in the same batch; the related-modules recheck reads only the importers on main): deliveries
    # of this batch linked by an import or a changed name are compiled together first (tools/batch_pairs.py); a pair that
    # breaks does not land together (the later one waits, or goes back with the compiler message)
    if plans:
        try:
            import batch_pairs as bp
            plans, pwait, pret = bp.split(plans, import_graph, log)
        except Exception as exc:  # noqa: BLE001   the global build still verifies the batch
            log("batch pair check failed, the batch lands as before |", repr(exc)[:300]); pwait, pret = [], []
        for p, _why in pwait + pret:
            for path in p["paths"]:
                if taken.get(path) == key(p):
                    taken.pop(path, None)
        for p, why in pwait:
            log("not in this batch", p["group"], p["item"], p["head"][:9], "|", why[:300])
        for p, why in pret:
            pre.done.pop(p["head"], None)
            give_back(p["group"], p["item"], p["head"], why, log)
    s2plans = []
    for x in s2ready:
        g, item, head = x["row"]["group"], x["row"]["item"], x["row"]["head"]
        clash = [p for p in s2b.paths_of(x) if p in taken]
        if clash:
            log("waits for the next batch", g, item, head[:9], "stage 2 |", f"{clash[0]} is written by {taken[clash[0]]} in this batch")
            continue
        texts = s2b.modules_of(x)
        try:
            cycles.refuse_missing(texts, base_modules, package_roots)
        except RuntimeError as exc:
            w = qwait.wait(exc, g, item, head)
            if w:
                log("not in this batch", g, item, head[:9], "stage 2 |", w[:300]); continue
            s2b.do_return(g, item, head, str(exc), log); continue
        cycle = cycles.closing_cycle(import_graph, texts)
        if cycle:
            log("waits for the next batch", g, item, head[:9], "stage 2 | import cycle:", " -> ".join(cycle)); continue
        import_graph = cycles.overlay(import_graph, texts)
        for p in s2b.paths_of(x):
            taken[p] = f"{g}/{item}"
        s2plans.append(x)
    if s2plans:
        n2 = len(s2plans)
        s2plans = s2b.validate(s2plans, log)     # the batch DAG check: only its offenders go back
        log(f"stage 2: {len(s2plans)} of {n2} checked deliveries pass the batch DAG check")
    if not plans and not s2plans:
        return None
    if target == OPEN and retry_round_open():
        log("a retry round opened during the checks: the batch lands when the round is green")
        return None
    t1 = time.time()
    if md.git("symbolic-ref", "-q", "--short", "HEAD", check=False) != md.MAIN:
        raise md.Fail(f"the working tree is not on {md.MAIN}")
    batch_id = time.strftime("%Y%m%dT%H%M%S", time.gmtime())
    entries, back, held = [], [], 0.0
    landing_marker = BD / 'landing.json'
    write_json(landing_marker, {'id': batch_id, 'started': ld.now()})
    tl = time.time()
    by_module = {}
    for nid, d in s2.nodes_at(s2.Git(ROOT), md.MAIN).items():
        l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
        if l.get("module"):
            by_module.setdefault(l["module"], []).append(nid)
    import_graph = pre.snapshot()
    expected_tip = pre.graph_tip
    base_modules = cycles.source_modules(ROOT, expected_tip)
    for plan in plans:
        g, item, head = plan["group"], plan["item"], plan["head"]
        pre.done.pop(head, None)     # landed, or checked again
        ids = [n for n in by_module.get(item, []) if n not in plan["D"]["nodes"]]
        plan["item_nodes"] = [p for p in (md.node_path(n) for n in ids) if p]
        try:
            # The graph is updated after each accepted delivery. The tip
            # records the previous delivery in this batch, so those known
            # commits do not invalidate the cycle check.
            current_tip = md.git('rev-parse', 'HEAD')
            if current_tip != expected_tip:
                # External source edits are overlaid outside the write lock.
                pre.import_graph, pre.graph_tip = import_graph, expected_tip
                import_graph = pre.snapshot(); expected_tip = pre.graph_tip
            try:
                cycles.refuse_missing({m["module"]: m["text"] for m in plan["D"]["modules"]}, base_modules, package_roots)
            except RuntimeError as exc:
                w = qwait.wait(exc, g, item, head)
                if w:
                    raise Wait(w) from exc
                raise Refuse(str(exc)) from exc
            plan["cycle_tip"] = expected_tip
            plan["cycle_tip_lean"] = md.git("rev-parse", f"{expected_tip}:lean")
            cycle = cycles.closing_cycle(import_graph, {m["module"]: m["text"] for m in plan["D"]["modules"]})
            if cycle: raise Wait("import cycle: " + " -> ".join(cycle))
            lock_started = time.time()
            with md.merge_lock():
                e = land_one(plan, batch_id)
                restore_after_fix(plan, log)
            held += time.time() - lock_started
            write_json(landing_marker, {"id": batch_id, "started": ld.now(), "entries": entries + [e]})
        except Wait as w:
            log("not in this batch", g, item, head[:9], "|", str(w)[:300]); continue
        except Refuse as f:
            back.append((g, item, head, str(f))); continue
        except md.Fail as f:
            log("landing failed, nothing changed; tried again in the next cycle", g, item, head[:9], "|", str(f)[:300]); continue
        entries.append(e)
        _qmark_at_landing("3", item, e.get("landing"))
        import_graph = cycles.overlay(import_graph,
                                      {m["module"]: m["text"] for m in plan["D"]["modules"]})
        expected_tip = e["commit"]
        pre.import_graph, pre.graph_tip = import_graph, expected_tip
        pre.graph_file = None
        log("landed", g, item, head[:9], "stage 3", f"batch {batch_id} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
    for plan in s2plans:
        g, item, head = plan["row"]["group"], plan["row"]["item"], plan["row"]["head"]
        try:
            lock_started = time.time()
            with md.merge_lock():
                e = s2b.land_one(plan, batch_id)
            held += time.time() - lock_started
            write_json(landing_marker, {"id": batch_id, "started": ld.now(), "entries": entries + [e]})
        except s2b.Stale as w:
            log("not in this batch", g, item, head[:9], "stage 2 |", str(w)[:300]); continue
        except md.Fail as f:
            log("landing failed, nothing changed; tried again in the next cycle", g, item, head[:9], "stage 2 |", str(f)[:300]); continue
        entries.append(e)
        _qmark_at_landing("2", item, e.get("landing"))
        import_graph = cycles.overlay(import_graph, s2b.modules_of(plan))
        expected_tip = e["commit"]
        pre.import_graph, pre.graph_tip = import_graph, expected_tip
        pre.graph_file = None
        log("landed", g, item, head[:9], "stage 2", f"batch {batch_id} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
    if entries:
        refresh_recovery_queue()
    for g, item, head, why in back:
        give_back(g, item, head, why, log)
    if not entries:
        landing_marker.unlink(missing_ok=True)
        return None
    b = {"id": batch_id, "time": ld.now(), "round": 0, "handled": [], "entries": entries,
         "check_seconds": round(t1 - t0, 1), "lock_seconds": round(held, 1)}
    if target == NEXT:
        b["pipelined_on"] = (read_json(OPEN) or {}).get("id")
    write_json(target, b)
    landing_marker.unlink(missing_ok=True)
    log(f"batch {batch_id}: {len(entries)} landed (checks {b['check_seconds']} s without a lock, lock held "
        f"{b['lock_seconds']} s); the global build verifies it"
        + (f" (pipelined on the build of batch {b['pipelined_on']})" if target == NEXT else ""))
    return b


def pending_merge_jobs(pre, cands, log) -> None:
    """2026-10-26 (the human): two checked deliveries waiting to land that write the same Lean file: the later one (in
    the order this batch takes them) gets a merge job onto the first one's text now, not after the first one landed."""
    try:
        plans = [pre.done[c["head"]][1] for c in cands if pre.done.get(c["head"], ("",))[0] == "ok"]
        mj.request_pending(plans, log)
    except Exception as exc:  # noqa: BLE001   never blocks a landing
        log("merge jobs: pending detection failed |", repr(exc)[:300])


def early_red_returned(g, item, head) -> bool:
    """2026-10-27: the delivery was returned to its writer while the build ran (tools/early_red.py); not again"""
    try:
        import early_red
        return early_red.returned_early(g, item, head)
    except Exception:  # noqa: BLE001
        return False


def give_back(g, item, head, why, log):
    """A delivery the tools refuse goes back to its group with their message (the human, 2026-10-12)."""
    if early_red_returned(g, item, head):
        log("ALREADY RETURNED while the build ran (tools/early_red.py)", g, item, str(head)[:9], "|", " ".join(why.split())[:200])
        return
    try:
        md.cmd_return(g, item, f"(the landing tools, head {head[:9]}) the delivery did not land: {why[:3000]}")
        log("RETURNED by the tools", g, item, head[:9], "|", " ".join(why.split())[:300])
    except Exception as e:  # noqa: BLE001
        if "merge.lock held" in str(e):
            log("lock busy, will retry", g, item, head[:9])
        else:
            log("RETURN FAILED", g, item, head[:9], "|", repr(e)[:200], "|", " ".join(why.split())[:200])


# ---------------------------------------------------------------- taking a landed delivery out

def undo_entries(entries, message, *, returned=False, repair_jobs=None):
    """Retry a stale preparation immediately, without another build or triage round."""
    for attempt in range(20):
        try:
            return _undo_entries(entries, message, returned=returned, repair_jobs=repair_jobs)
        except recovery.TipMoved:
            if attempt == 19: raise


def _undo_entries(entries, message, *, returned=False, repair_jobs=None):
    """Prepare outside locks; restore delivery records and sources in a single commit.

    See batch_recovery's docstring for the records derived from land_one and
    merge_delivery. Substantive later edits request whole-batch withdrawal.
    """
    if not entries: return
    tip = md.git("rev-parse", "HEAD")
    chained = []
    if ld.merge_queue():
        # merge queue: the Lean files go back hard to their version before the landing (and later landings of the
        # same files go too); the bookkeeping is inverted leniently, so nothing can conflict
        t0 = time.time()
        dropped, restore_to, notes = ld.drop_plan([e["landing"] for e in entries])
        kept = []
        prepared = recovery.inverse(ROOT, [e["commit"] for e in entries], skip_lean=True, lenient=kept)
        lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
        for rel, data in restore_to.items():
            prepared[f"{lean_rel}/{rel}"] = data
        ids = {e["landing"] for e in entries}
        chained = [r for r in dropped if r["id"] not in ids]
        for x in notes + kept:
            MQ_LOG(f"take-out: {x}")
        MQ_LOG(f"take-out of {len(entries)} delivery(ies): {len(restore_to)} file(s) restored, {len(chained)} later "
               f"landing(s) with them, prepared in {time.time() - t0:.1f} s")
    else:
        prepared = recovery.inverse(ROOT, [e["commit"] for e in entries], imports_only=bool(returned))
    # Audits/proved flags computed after landing describe the removed source.
    # Restore those fields from the pre-landing node; keep independent metadata.
    for e in entries:
        for path in recovery.git(ROOT, 'diff-tree', '--no-commit-id', '--name-only', '-r', e['commit']).decode().splitlines():
            if not path.startswith('dag/nodes/') or path not in prepared or prepared[path] is None: continue
            old = recovery.blob(ROOT, e['commit'] + '^', path)
            if old is None: continue
            a, cur = json.loads(old), json.loads(prepared[path])
            for field in ('lean_audit', 'proved', 'proved_proof'):
                if field in a: cur[field] = a[field]
                else: cur.pop(field, None)
            prepared[path] = (json.dumps(cur, ensure_ascii=False, indent=2) + '\n').encode()
    recs = []
    for e in entries:
        rid = e["landing"]
        r = ld.read_json(ld.REQUESTS / f"{rid}.json") or ld.read_json(ld.DONE / f"{rid}.json")
        if r:
            r = dict(r)
            r.update(result="reverted" if returned else "withdrawn", reason=message, closed=ld.now())
            r["sorry_allowed"] = {}
            for f in r['files']:
                path = 'lean/' + f['path']
                data = prepared.get(path)
                if path not in prepared:
                    p = ROOT / path; data = p.read_bytes() if p.is_file() else None
                r['sorry_allowed'][f['module']] = sorted(k for k, d in s3.decl_table((data or b'').decode()).items() if d['sorry'])
                f['sha'] = __import__('hashlib').sha256(data).hexdigest() if data is not None else None
            recs.append(r)
        claim = 'coord/claims/' + e['item'].replace('/', '__') + '.lock'
        if e.get('claim'):
            p = ROOT / claim
            if not p.exists(): prepared[claim] = e['claim'].encode()
        entry_returned = returned is True or isinstance(returned, dict) and key(e) in returned
        entry_message = returned.get(key(e), message) if isinstance(returned, dict) else message
        if recs and recs[-1]["id"] == rid:
            recs[-1]["result"] = "reverted" if entry_returned else "withdrawn"
            recs[-1]["reason"] = entry_message
        if entry_returned and not early_red_returned(e['group'], e['item'], e.get('head')):   # early: entry kept
            p, before, parts = md.return_entries(e['group'], e['item'])
            if p.relative_to(ROOT).as_posix() in prepared:
                parts = re.split(r'(?=^## )', prepared[p.relative_to(ROOT).as_posix()].decode(), flags=re.M)
            kept = ''.join(x for x in parts if not x.startswith(f"## {e['item']} ("))
            prepared[p.relative_to(ROOT).as_posix()] = (kept.rstrip() + f"\n\n## {e['item']} ({ld.now()}, branch head {e['head'][:9]})\n\n{entry_message}\n").encode()
    # Reserve repairs atomically with take-out; local outbox requests become
    # runnable only when this dedicated claim appears. No original-group return.
    for e in entries:
        job = (repair_jobs or {}).get(key(e))
        if not job: continue
        cp = repairs.claim_path(e['item'])
        current = repairs.read(cp)
        if current and current.get('who') not in (e['group'], job['group']):
            # another group already works on the item (2026-10-13 22:46: raising here withdrew a whole batch):
            # no repair job, that group's work stands; the delivery is still taken out
            repair_jobs.pop(key(e), None)
            continue
        prepared[cp.relative_to(ROOT).as_posix()] = json.dumps(dict(
            who=job['group'], t=time.time(), since=ld.now(), repair=job['id'])).encode()
        rp, before, parts = md.return_entries(e['group'], e['item'])
        rel = rp.relative_to(ROOT).as_posix()
        text = (prepared.get(rel) or (before or '').encode()).decode()
        prepared[rel] = ''.join(x for x in re.split(r'(?=^## )', text, flags=re.M)
                               if not x.startswith(f"## {e['item']} (")).encode()
    ledger = prepared.get('coord/ledger.md', (ROOT / 'coord/ledger.md').read_bytes()) or b''
    prepared['coord/ledger.md'] = ledger + f"\n- {time.strftime('%H:%M')} L: {message[:180]}\n".encode()
    with md.merge_lock():
        with ld.tree_lock():
            recovery.commit_inverse(ROOT, prepared, tip, 'Take out batch deliveries' if returned else 'Withdraw unverified batch')
            for r in recs:
                ld.write_json(ld.DONE / f"{r['id']}.json", r)
                (ld.REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
                shutil.rmtree(ld.BACKUP / r['id'], ignore_errors=True); shutil.rmtree(ld.STAGED / r['id'], ignore_errors=True)
                ld.drop_mirror(r['group'], [f['path'] for f in r['files']])
            if chained:
                ld.drop_close(chained, message)
                for r in chained:
                    MQ_LOG(f"take-out: landing {r['id']} of {r['group']} went with them (same files changed after)")
    for r in chained:
        if r.get('delivery'):
            return_record(r, message, MQ_LOG_FN)
    # Queue calculation is source-only and deliberately outside both write locks.
    refresh_recovery_queue()


def refresh_recovery_queue():
    r = subprocess.run([sys.executable, 'tools/queue.py', 'write'], cwd=ROOT, capture_output=True)
    if r.returncode:
        raise md.Fail('queue refresh after take-out failed: ' + r.stderr.decode(errors='replace')[-300:])
    paths = ['coord/queue.tsv', 'coord/queue.md', 'coord/blueprint-index.tsv']
    with md.merge_lock():
        if md.git('status', '--porcelain', '--', *paths):
            md.git_retry('add', '--', *paths)
            md.git_retry('commit', '-q', '-m', 'Queue after batch recovery' + recovery.TRAILER, '--', *paths)
    # 2026-10-27 (lead): retag right after the queue write. Only ~/cc1/sorry-route-loop.sh ran tools/tag_batches.py, so items
    # new in this queue were `untagged` (no dispatcher lane) until its next cycle; 53 sat unstarted 06:29-06:37 behind a
    # sorry-route refresh. Detached at nice 10 (about a minute); the tag file is replaced atomically by the script.
    try:
        subprocess.Popen(['nice', '-n', '10', sys.executable, 'tools/tag_batches.py'], cwd=ROOT, stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
    except OSError:
        pass


def unland(e: dict, reason: str, ledger: str) -> None:
    undo_entries([e], reason, returned=True)


def withdraw(b, reason, log):
    """Last resort only: transactional restoration cannot remove a smaller set."""
    alert(b['id'], '?', reason, 'restore batch transaction; no bisection')
    active = [e for e in b['entries'] if e['state'] in ('landed', 'stuck')]
    undo_entries(active, f"batch {b['id']} withdrawn: {reason}")
    defer_entries(active)
    b.pop('triage', None)
    b['await_recovery'] = True
    write_json(OPEN, b)
    log(f"batch {b['id']} withdrawn transactionally; no halves; build restored tree")


def defer_entries(entries):
    for e in entries:
        if e.get('stage') == '2':
            s2b.requeue(e); e['state'] = 'waiting'; continue
        br = md.branch_of(e['group'], e['item'])
        if not md.has_ref('refs/heads/' + br): md.git('branch', br, e['head'])
        e['state'] = 'waiting'
        write_json(marker(e['group'], e['item']), {**e, 'overrides': e.get('overrides', {}),
                   'verdict': 'PASS', 'time': ld.now()})


# ---------------------------------------------------------------- a red build

HEADER = re.compile(r"^[✔⚠✖ℹ] \[\d+/\d+\] \w+ (\S+)", re.M)


def log_blocks(text: str) -> dict[str, str]:
    """module -> what Lake printed for its failed job."""
    out = {}
    hs = list(HEADER.finditer(text))
    for k, h in enumerate(hs):
        if not h.group(0).startswith("✖"):
            continue
        end = hs[k + 1].start() if k + 1 < len(hs) else len(text)
        blk = text[h.start():end]
        cut = blk.find("\nSome required")
        blk = blk if cut < 0 else blk[:cut]
        out[h.group(1)] = "\n".join(l for l in blk.split("\n") if not l.startswith("trace: ")).strip()
    return out


def library_imports() -> dict:
    # Attribution must use the current batch tree, never a stale buildtree.
    return cycles.graph(li.LEAN)


def chain(src: str, dst: set, imports: dict) -> list[str]:
    """One import path from `src` to a module of `dst`."""
    prev, todo = {src: None}, [src]
    while todo:
        m = todo.pop(0)
        if m in dst and m != src:
            out = []
            while m is not None:
                out.append(m); m = prev[m]
            return out[::-1]
        for i in sorted(imports.get(m, ())):
            if i not in prev:
                prev[i] = m; todo.append(i)
    return []


def triage(b: dict, last: dict, imports=None) -> dict:
    """The mechanical part: {decisions: [{failure, case, return: [G/item], reason, message}], open: [{failure,
    suspects: [G/item], message, others}], unattributed: [module]}."""
    entries = [e for e in b['entries'] if e['state'] == 'landed']
    # 2026-10-21: only the landings the red build contained can have caused it (a landing after its snapshot, e.g. a
    # pipelined batch, was not compiled by it)
    inc = set(last.get('included') or [])
    if inc and any(e['landing'] in inc for e in entries):
        entries = [e for e in entries if e['landing'] in inc]
    text = (ld.LOCAL / 'build.log').read_text(errors='ignore') if (ld.LOCAL / 'build.log').exists() else ''
    blocks = log_blocks(text)
    if imports is None: imports = library_imports()
    failures = list(dict.fromkeys(list(last.get('failing') or []) +
                                  [c['module'] for c in last.get('batch_checks') or []]))
    messages = {m: blocks.get(m) or '\n'.join(last.get('errors') or []) for m in failures}
    messages.update({c['module']: c['message'] for c in last.get('batch_checks') or []})
    deltas = {}
    def changes(e, m):
        stop_checkpoint()
        k = (e["commit"], m)
        if k in deltas: return deltas[k]
        path = s3.path_of_module(m)
        a, z = recovery.blob(ROOT, e['commit'] + '^', path), recovery.blob(ROOT, e['commit'], path)
        deltas[k] = recovery.interface_delta(a.decode() if a is not None else None,
                                               z.decode() if z is not None else None)
        return deltas[k]
    T = {'decisions': [], 'open': [], 'unattributed': [] if failures else ['?']}
    for o in recovery.select(entries, failures, imports, changes, messages, checkpoint=stop_checkpoint):
        suspects = [key(e) for e in o['suspects']]
        if not suspects:
            T['unattributed'].append(o['failure'])
        elif len(suspects) <= 3:
            T['decisions'].append({'failure': o['failure'], 'case': o['case'],
                'return': suspects, 'reason': '', 'message': o['message']})
        else:
            T['open'].append({'failure': o['failure'], 'writer': None, 'suspects': suspects,
                'message': o['message'], 'others': [],
                'chains': {key(e): chain(o['failure'], set(e['modules']), imports) for e in o['suspects']}})
    return T


PROMPT = """You are the triage agent of a red global build of the Lean project weil-conjectures-sheaf. You READ and DECIDE; you
change nothing: no file write outside this directory, no git command that changes anything. A script acts on your answer.

A batch of deliveries was written into the library together, and the build of the whole library failed. Each delivery
was compiled by its group against the library as it was BEFORE the batch. For each failure below, the tools could not
tell which delivery of the batch is at fault. Decide it from the compiler's message, the diffs and the imports.

For each failing module choose one case:
  "own-fault"         the failing module was delivered in this batch and its own delivered text is wrong (the error does
                      not come from another delivery's change). Return the delivery that wrote it.
  "breaker"           the failing module is correct against the library before the batch and fails because another
                      delivery of the batch changed something it uses, and that change is NOT one the rest of the
                      library has to follow (an accident: a renamed or removed declaration, a changed signature or
                      instance that the delivery did not have to change, a name it now declares twice). Return the
                      delivery that made the change.
  "dependent-adapts"  as "breaker", but the other delivery's change is a legitimate change of an interface (a corrected
                      statement or definition, with its change record) and stays; the failing module was delivered in
                      this batch and has to be adapted to it. Return the delivery that wrote the failing module, and say
                      in the reason exactly what it has to adapt to. If the failing module was NOT delivered in this
                      batch, this case is not available: the delivery that changed the interface did not adapt its
                      user and is returned ("breaker").
  "not-the-batch"     allowed ONLY when the failing module and all its imports are byte-identical to the last green commit, mechanically checked by the tools. Return nothing.
Return as few deliveries as make the build pass. Only suspects listed for a failure may be returned for it.

{failures}

The diffs of the suspect deliveries (the Lean files only):

{diffs}

Your answer ends with ONE line of JSON and nothing after it:
{{"decisions": [{{"failure": "<failing module>", "case": "own-fault" | "breaker" | "dependent-adapts" | "not-the-batch", "return": ["<G>/<module>", ...], "reason": "<two or three sentences for the group that gets the delivery back: what is wrong and what to change>"}}, ...]}}
One entry per failing module listed above."""


def write_request(b: dict, T: dict) -> pathlib.Path:
    d = TRIAGE / f"{b['id']}-r{b['round'] + 1}"
    d.mkdir(parents=True, exist_ok=True)
    ent = {key(e): e for e in b["entries"]}
    fl, sus = [], []
    for o in T["open"]:
        s = [f"## Failing module {o['failure']}"
             + (f" (delivered in this batch by {o['writer']})" if o["writer"] else " (not delivered in this batch)"),
             "Suspects: " + ", ".join(o["suspects"])]
        for k, ch in o["chains"].items():
            s.append(f"Imports reaching the modules of {k} ({', '.join(ent[k]['modules'])}): " + (" -> ".join(ch) or "(indirect)"))
        if o["others"]:
            s.append("Other landings in the same build that it also depends on (not of this batch, not yours to return): " + "; ".join(o["others"]))
        s.append("Compiler message:\n```\n" + o["message"][:8000] + "\n```")
        fl.append("\n".join(s))
        sus += [k for k in o["suspects"] if k not in sus]
    diffs = []
    for k in sus:
        e = ent[k]
        t = md.git("show", "--format=", e["commit"], "--", "lean/", check=False)
        diffs.append(f"### {k} (modules {', '.join(e['modules'])}; reviewer {e['reviewer']}; landing kind {e['kind']})\n```diff\n"
                     + t[:60000] + ("\n... (cut)" if len(t) > 60000 else "") + "\n```")
    (d / "meta.json").write_text(json.dumps({"batch": b["id"], "open": T["open"]}, ensure_ascii=False, indent=1))
    tmp = d / "request.tmp"
    tmp.write_text(PROMPT.format(failures="\n\n".join(fl), diffs="\n\n".join(diffs)))
    os.replace(tmp, d / "request.md")
    return d


def verdict_decisions(T: dict, v) -> list[dict]:
    """The agent's decisions, checked; a failure without a usable decision returns all its suspects."""
    got = {}
    for x in (v or {}).get("decisions") or [] if isinstance(v, dict) else []:
        if isinstance(x, dict) and isinstance(x.get("failure"), str):
            got[x["failure"]] = x
    out = []
    for o in T["open"]:
        x = got.get(o["failure"])
        ret = [k for k in (x or {}).get("return") or [] if k in o["suspects"]] if x else None
        case = (x or {}).get("case")
        if x and ret and case in ("own-fault", "breaker", "dependent-adapts") and not (case == "dependent-adapts" and ret != [o["writer"]]):
            out.append({"failure": o["failure"], "case": case, "return": ret, "reason": str(x.get("reason") or ""), "message": o["message"], "by": "codex"})
        else:
            out.append({"failure": o["failure"], "case": "undecided", "return": list(o["suspects"]),
                        "reason": "the triage gave no usable decision for this failure, so every delivery of the batch that may have caused it is returned",
                        "message": o["message"], "by": "fallback"})
    return out


def execute(b: dict, decisions: list[dict], log, deferred=(), imports=None) -> None:
    ent = {key(e): e for e in b["entries"]}
    per = {}
    for d in decisions:
        for k in d["return"]:
            per.setdefault(k, []).append(d)
        if not d["return"]:
            log(f"batch {b['id']} triage: {d['failure']} {d['case']} ({d.get('by', 'tools')}); nothing returned |", d.get("reason", "")[:200])
    active = [e for e in b['entries'] if e['state'] == 'landed']
    suspects = [e for e in active if key(e) in per]
    if imports is None: imports = library_imports()
    waiting = [e for e in active if set(e['modules']) & set(deferred) and e not in suspects]
    # 2026-10-25 (the human: a red round removes only what caused the errors): a delivery goes out with a culprit only
    # when its own files need the culprit's version (chain_dependents); an importer that merely could not be built
    # stays and the retry verifies it. recovery.dependents (every transitive importer) had deferred 20 innocent
    # deliveries of batch 20261025T070805 with the two overtime modules.
    deps = waiting + chain_dependents(active, suspects + waiting, imports)
    messages = {}
    for e in suspects:
        parts = []
        for d in per[key(e)]:
            modules = set(e['modules']) & (li.closure(d['failure'], imports, {}) | {d['failure']})
            parts.append(d.get('message', '') + '\n' + d.get('reason', ''))
            for m in sorted(modules):
                if m == d['failure']:
                    continue   # the delivery's own module fails: the compiler message above says why
                parts.append(f"your change of {m} broke its importer {d['failure']}: adapt the importers in the same delivery or do not change what they use")
        messages[key(e)] = '\n\n'.join(parts)
    chosen = [e for e in active if e in suspects or e in deps]
    if not chosen:
        b['await_recovery'] = True
        b.pop('triage', None)
        write_json(OPEN, b)
        return
    extra = []
    if ld.merge_queue():
        # deliveries of this batch that changed a culprit's file after it go out with it (hard restore), returned
        by_landing = {e['landing']: e for e in active}
        for r in ld.drop_plan([e['landing'] for e in chosen])[0]:
            e = by_landing.get(r['id'])
            if e is not None and e not in chosen:
                extra.append(e); chosen.append(e)
                messages[key(e)] = ("(the batch landing) taken out again: a delivery of the same batch that broke the global build "
                                    "changed the same file(s) before it, so it goes out with it. Deliver again on the current library.")
                log(f"batch {b['id']}: {key(e)} goes out with the culprit (same files changed after it)")
    tip = (ld.read_json(ld.B / 'last.json') or {}).get('commit') or md.git('rev-parse', 'HEAD')
    # a stage-2 delivery goes back to its writer (its claim is restored), no repair job (2026-10-25)
    # 2026-10-26 (rule of 10-24: a delivery returned by the global build is repaired in the SAME Codex session that
    # delivered it): stage 3 too. The repair queue (repairs.txt) handed every stage-3 culprit of 10-25/26 to another
    # group as new work (14 of 14 lost their session). The writer's claim is restored and the reason goes to
    # coord/returns/<group>.md; the group's dispatcher resumes the delivering session as a repair.
    for e in suspects:
        if e.get('commit'):
            messages[key(e)] += (f"\n\nThe landed change was taken out of the library (delivery branch gone): recover it with "
                                 f"`git show {e['commit'][:10]} -- lean dag/nodes coord/changes`.")
    repair_jobs = {}
    try:
        undo_entries(chosen, f"batch {b['id']} dependency take-out", returned=messages, repair_jobs=repair_jobs)
    except recovery.Conflict as x:
        # 2026-10-19: this used to withdraw the whole batch, whose inverse conflicted the same way; the step raised,
        # nothing was recorded, and the lander retried every two minutes for hours while live stayed red.
        conflict_fallback(b, active, suspects, chosen, per, messages, repair_jobs, x, log, imports)
        return
    for e in extra:
        e['state'] = 'returned'; e['why'] = messages[key(e)]
        log('TAKEN OUT WITH THE CULPRIT; RETURNED', key(e))
    for e in suspects:
        e['state'] = 'returned'; e['why'] = messages[key(e)]
        job = repair_jobs.get(key(e))
        if job is None:
            holder = repairs.read(repairs.claim_path(e['item'])).get('who')
            log('TAKEN OUT; RETURNED TO ITS WRITER' if holder == e['group'] else f'TAKEN OUT; RETURNED, BUT ITEM HELD BY {holder}',
                key(e), '|', messages[key(e)][:300]); continue
        if job is None:   # another group already holds the item (skipped in _undo_entries): its work stands
            log('TAKEN OUT; HELD BY ANOTHER GROUP, NO REPAIR JOB', key(e), '|', messages[key(e)][:300]); continue
        e['repair'] = job['id']
        log('TAKEN OUT; REPAIR QUEUED', key(e), job['group'], '|', messages[key(e)][:300])
    defer_entries(deps)
    b['round'] += 1
    b['await_recovery'] = True
    b.pop('triage', None)
    write_json(OPEN, b)


# ---------------------------------------------------------------- a take-out that conflicts with later edits

ERROR_AT = re.compile(r"^error: (\S+?\.lean):(\d+):(\d+): ?(.*)$", re.M)
PROOF_KW = ("theorem", "lemma")


def chain_dependents(entries, removed, imports) -> list:
    """The deliveries of `entries` (not in `removed`) whose own modules directly import a module of a removed delivery
    and need its version: the file goes away (the landing created it), or the importer uses a name the take-out removes
    (the landing's `changed`, or a declaration its version has and the previous one lacks). Transitive through the
    deliveries so added; an importer that only sits above a removed module is kept."""
    out, gone_ids = [], {key(e) for e in removed}
    names_of, gone_mods = {}, set()

    def _add(e):
        rec = ld.read_json(ld.REQUESTS / f"{e['landing']}.json") or ld.read_json(ld.DONE / f"{e['landing']}.json") or {}
        for f in rec.get('files') or []:
            m = f.get('module')
            if not m:
                continue
            if not f.get('existed', True):
                gone_mods.add(m); continue
            ns = {str(c).split()[0] for c in rec.get('changed') or [] if str(c).strip() and not str(c).startswith('(')}
            try:
                st, bk = ld.STAGED / rec['id'] / f['path'], ld.BACKUP / rec['id'] / f['path']
                new = st.read_text(errors='ignore') if st.is_file() else None
                old = bk.read_text(errors='ignore') if bk.is_file() else None
                if new is not None and old is not None:
                    ns |= ({c['name'] for c in li.commands(new) if c['name']} - {c['name'] for c in li.commands(old) if c['name']})
            except Exception:  # noqa: BLE001
                pass
            names_of.setdefault(m, set()).update(ns)
        for m in e.get('modules') or []:
            names_of.setdefault(m, set())

    for e in removed:
        _add(e)
    changed = True
    while changed:
        changed = False
        for e in entries:
            if key(e) in gone_ids:
                continue
            hit = False
            for m in e.get('modules') or []:
                below = set(imports.get(m) or ()) & (set(names_of) | gone_mods)
                if not below:
                    continue
                if below & gone_mods:
                    hit = True; break
                ns = set().union(*(names_of.get(x, set()) for x in below))
                if not ns:
                    continue
                p = li.file_of(m)
                try:
                    src = li.strip(p.read_text(errors='ignore')) if p.is_file() else ''
                except OSError:
                    src = ''
                used = set()
                for tok in _IDENT.findall(src):
                    parts = tok.split('.')
                    used |= {'.'.join(parts[k:]) for k in range(len(parts))}
                if any(n in used or n.split('.')[-1] in used and len(n.split('.')[-1]) > 3 for n in ns):
                    hit = True; break
            if hit:
                gone_ids.add(key(e)); out.append(e); _add(e); changed = True
    return out


def conflicting_entries(entries) -> dict:
    """key -> Conflict message for each entry whose own inverse cannot be prepared on the current tree."""
    out = {}
    for e in entries:
        try:
            recovery.inverse(ROOT, [e["commit"]])
        except recovery.Conflict as x:
            out[key(e)] = str(x)
    return out


def build_errors(modules) -> dict:
    """module -> [(line, col, message)] of the red build, from Lake's log (local/builds/build.log)."""
    text = (ld.LOCAL / "build.log").read_text(errors="ignore") if (ld.LOCAL / "build.log").exists() else ""
    blocks, out = log_blocks(text), {}
    for m in modules:
        rel = m.replace(".", "/") + ".lean"
        seen = out.setdefault(m, [])
        for x in ERROR_AT.finditer(blocks.get(m, "")):
            if x.group(1) == rel and (int(x.group(2)), int(x.group(3))) not in {(a, c) for a, c, _ in seen}:
                seen.append((int(x.group(2)), int(x.group(3)), x.group(4)))
    return out


def _offset(text: str, line: int, col: int) -> int:
    lines = text.split("\n")
    return sum(len(l) + 1 for l in lines[:line - 1]) + col


def fail_forward_text(text: str, errors, olds) -> tuple[str, list[str], list[str]]:
    """Make one failing module compile again without touching what other modules see.

    errors: [(line, col, message)]; olds: [(label, text before the culprit)]. A failing proof body of a theorem/lemma
    becomes `sorry`; a failing definition, instance or statement gets back its text from before the culprit (never
    hollowed). Returns (new text, actions, unfixable)."""
    decls = s2.declarations(text)
    edits, actions, unfixable = {}, [], []
    for line, col, msg in errors:
        off = _offset(text, line, col)
        d = next((d for d in decls if d["start"] <= off < d["end"]), None)
        if d is None:
            unfixable.append(f"{line}:{col} outside every declaration: {msg}"); continue
        k = d["name"] or f"instance {d['statement']}"
        if d["start"] in edits:
            continue
        if d["kw"] in PROOF_KW and d["sig_end"] < d["end"] and off >= d["sig_end"]:
            body = text[d["sig_end"]:d["end"]]
            tail = body[len(body.rstrip()):]
            edits[d["start"]] = (d["sig_end"], d["end"], ":= by\n  sorry" + (tail if "\n" in tail else "\n\n"))
            actions.append(f"proof of {k} replaced by sorry ({line}:{col} {msg[:120]})")
            continue
        for label, old in olds:
            od = next((x for x in s2.declarations(old or "") if (x["name"] or f"instance {x['statement']}") == k), None)
            if od is not None:
                piece = old[od["start"]:od["end"]]
                tail = text[d["start"]:d["end"]]
                tail = tail[len(tail.rstrip()):]
                edits[d["start"]] = (d["start"], d["end"], piece.rstrip() + (tail if "\n" in tail else "\n\n"))
                actions.append(f"{d['kw']} {k} restored to its text before {label} ({line}:{col} {msg[:120]})")
                break
        else:
            unfixable.append(f"{d['kw']} {k} ({line}:{col} {msg[:160]}): no proof body to replace and no earlier text")
    out = text
    for a, z, rep in sorted(edits.values(), reverse=True):
        out = out[:a] + rep + out[z:]
    return out, actions, unfixable


def fail_forward(b, entries, per, messages, log) -> dict:
    """The culprits' changes cannot be taken out (later edits overlap them): repair their failing modules in place
    and give the deliveries back. Returns key -> {actions, unfixable} for the entries handled; one commit."""
    failing = sorted({d["failure"] for e in entries for d in per[key(e)]})
    errors = build_errors(failing)
    prepared, done, records = {}, {}, []
    for e in entries:
        k = key(e)
        acts, bad = [], []
        for m in sorted({d["failure"] for d in per[k]}):
            rel = "lean/" + m.replace(".", "/") + ".lean"
            cur = prepared.get(rel)
            cur = cur.decode() if cur is not None else ((ROOT / rel).read_text() if (ROOT / rel).is_file() else None)
            if cur is None or not errors.get(m):
                bad.append(f"{m}: no file or no located compiler error"); continue
            olds = []
            if rel in recovery.git(ROOT, "diff-tree", "--no-commit-id", "--name-only", "-r", e["commit"]).decode().split():
                before = recovery.blob(ROOT, e["commit"] + "^", rel)
                olds.append((f"{k} (landing {e['landing']})", before.decode() if before is not None else None))
            new, a, u = fail_forward_text(cur, errors[m], olds)
            if new != cur:
                prepared[rel] = new.encode()
            acts += [f"{m}: {x}" for x in a]; bad += [f"{m}: {x}" for x in u]
        done[k] = {"actions": acts, "unfixable": bad}
        for x in acts: log("FAIL-FORWARD", k, "|", x)
        for x in bad: log("FAIL-FORWARD cannot fix", k, "|", x)
        if not acts:
            continue        # nothing changed for this delivery: it stays landed, no record is touched
        why = (messages.get(k, "") + "\n\nThe delivery could not be taken out (" + e.get("conflict", "a later edit overlaps it")
               + "), so the failing declarations were repaired in place instead:\n" + "\n".join("- " + x for x in acts or ["(nothing)"])
               + "\nRedo the work against the current library and deliver again.")
        rid = e["landing"]
        r = ld.read_json(ld.REQUESTS / f"{rid}.json") or ld.read_json(ld.DONE / f"{rid}.json")
        if r:
            r = dict(r)
            r.update(result="reverted", reason=why[:6000], closed=ld.now(), fail_forward=acts)
            r["sorry_allowed"] = {}
            for f in r.get("files", []):
                path = "lean/" + f["path"]
                data = prepared.get(path)
                if data is None:
                    q = ROOT / path; data = q.read_bytes() if q.is_file() else None
                r["sorry_allowed"][f["module"]] = sorted(x for x, d in s3.decl_table((data or b"").decode()).items() if d["sorry"])
                f["sha"] = __import__("hashlib").sha256(data).hexdigest() if data is not None else None
            records.append(r)
        claim = "coord/claims/" + e["item"].replace("/", "__") + ".lock"
        if e.get("claim") and not (ROOT / claim).exists():
            prepared[claim] = e["claim"].encode()
        rp, before, _ = md.return_entries(e["group"], e["item"])
        rrel = rp.relative_to(ROOT).as_posix()
        text = (prepared.get(rrel) or (before or "").encode()).decode()
        kept = "".join(x for x in re.split(r"(?=^## )", text, flags=re.M) if not x.startswith(f"## {e['item']} ("))
        prepared[rrel] = (kept.rstrip() + f"\n\n## {e['item']} ({ld.now()}, branch head {e['head'][:9]})\n\n{why}\n").encode()
        name = f"coord/changes/failforward-{b['id']}-{e['group']}-{e['item'].replace('/', '__')}.md"
        prepared[name] = (f"Fail-forward of a red batch build (batch {b['id']}, landing {rid})\n\n## Reason\n\n"
                          f"The global build failed in {', '.join(sorted({d['failure'] for d in per[k]}))}; the triage named {k}. "
                          f"Taking the delivery out conflicts with later edits ({e.get('conflict', '?')}).\n\n## Old\n\n"
                          f"landing commit {e['commit']}\n\n## New\n\n" + "\n".join("- " + x for x in acts or ["(nothing)"])
                          + ("\n\nNot fixable here:\n" + "\n".join("- " + x for x in bad) if bad else "")
                          + f"\n\n## Users\n\n{', '.join(sorted({d['failure'] for d in per[k]}))}\n\n## Status\n\n"
                          f"reverted {ld.now()} (fail-forward by tools/batch_land.py; the delivery is back with {e['group']})\n").encode()
    if not any(p.startswith("lean/") for p in prepared):
        return done
    tip = md.git("rev-parse", "HEAD")
    ledger = (ROOT / "coord/ledger.md").read_bytes() if (ROOT / "coord/ledger.md").exists() else b""
    prepared["coord/ledger.md"] = ledger + f"\n- {time.strftime('%H:%M')} L: batch {b['id']} fail-forward of {', '.join(done)}\n".encode()
    with md.merge_lock():
        with ld.tree_lock():
            recovery.commit_inverse(ROOT, prepared, tip, f"Fail forward in the red build of batch {b['id']}: "
                                    + ", ".join(done) + " repaired in place and returned")
            for r in records:
                ld.write_json(ld.DONE / f"{r['id']}.json", r)
                (ld.REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
                ld.drop_mirror(r["group"], [f["path"] for f in r.get("files", [])])
    refresh_recovery_queue()
    return done


def conflict_fallback(b, active, suspects, chosen, per, messages, repair_jobs, conflict, log, imports) -> None:
    """undo_entries raised Conflict. (a) Later import-only edits never conflict (batch_recovery.import_delta).
    (b) Take out what can be taken out; the suspects whose own take-out conflicts are fixed forward in their failing
    modules and returned; a dependent whose take-out conflicts stays. Every decision is one log line; nothing loops:
    the next build verifies."""
    t0 = time.time()
    log(f"batch {b['id']}: take-out conflict ({conflict}); falling back")
    bad = conflicting_entries(chosen)
    for k, why in bad.items():
        log(f"batch {b['id']}: CONFLICT {k} cannot be taken out: {why[:200]}")
    stuck = [e for e in suspects if key(e) in bad]
    movable = [e for e in suspects if key(e) not in bad]
    # the dependents and deferred closures chosen for the take-out go too, unless their own take-out conflicts
    deps = [e for e in chosen if e not in suspects and key(e) not in bad]
    taken = []
    if movable or deps:
        jobs = {key(e): repair_jobs[key(e)] for e in movable if key(e) in repair_jobs}
        try:
            undo_entries(movable + deps, f"batch {b['id']} dependency take-out", returned={key(e): messages[key(e)] for e in movable},
                         repair_jobs=jobs)
            taken = movable
            for e in movable:
                e['state'] = 'returned'; e['why'] = messages[key(e)]
                job = jobs.get(key(e))
                if job is None:
                    log('TAKEN OUT; HELD BY ANOTHER GROUP, NO REPAIR JOB', key(e))
                else:
                    e['repair'] = job['id']; log('TAKEN OUT; REPAIR QUEUED', key(e), job['group'])
            defer_entries(deps)
            for e in deps: log(f"batch {b['id']}: deferred (imports a removed delivery)", key(e))
        except recovery.Conflict as x:
            log(f"batch {b['id']}: take-out of the non-conflicting suspects conflicts too ({x}); all suspects fail forward")
            stuck, deps = suspects, []
    # a staged repair job of a delivery that stays in the library would tell a worker it was taken out (2026-10-19)
    for e in suspects:
        job = repair_jobs.get(key(e))
        if job and e not in taken:
            jp = repairs.JOBS / (job['id'] + '.json')
            if (repairs.read(jp) or {}).get('state') == 'pending':
                jp.unlink(missing_ok=True)
    for e in active:
        if key(e) in bad and e not in suspects:
            log(f"batch {b['id']}: dependent {key(e)} stays in the library (its take-out conflicts); the build verifies it")
    if stuck:
        for e in stuck:
            e['conflict'] = bad.get(key(e), str(conflict))
        try:
            res = fail_forward(b, stuck, per, messages, log)
        except recovery.Conflict as x:   # the tip moved on these paths; the next red build tries again
            res = {}
            log(f"batch {b['id']}: fail-forward could not be written ({x}); next step retries")
            cur = ld.read_json(ld.B / 'last.json') or {}
            b['handled'] = [h for h in b['handled'] if h != cur.get('time')]
            b['handled_sources'] = [h for h in b.get('handled_sources', []) if h != cur.get('source_fingerprint')]
        for e in stuck:
            r = res.get(key(e))
            if r is None or not r['actions']:
                alert(b['id'], key(e), 'take-out conflicts and fail-forward changed nothing: ' + '; '.join((r or {}).get('unfixable', []))[:300],
                      'maintainer fix of the failing module')
                log(f"batch {b['id']}: ALERT {key(e)} stays landed: nothing could be repaired in place")
                continue
            e['state'] = 'returned'; e['why'] = 'fail-forward: ' + '; '.join(r['actions'])[:2000]
            e['fail_forward'] = r
            log(f"batch {b['id']}: RETURNED (fail-forward) {key(e)}: {len(r['actions'])} declaration(s) repaired in place"
                + (f", {len(r['unfixable'])} not fixable here" if r['unfixable'] else ""))
            if r['unfixable']:
                alert(b['id'], key(e), 'fail-forward left errors: ' + '; '.join(r['unfixable'])[:300], 'maintainer fix of the failing module')
    b['round'] += 1
    b['await_recovery'] = True
    b.pop('triage', None)
    write_json(OPEN, b)
    log(f"batch {b['id']}: conflict fallback done in {time.time() - t0:.1f} s; the next build verifies")


def _qmark_rework(r):
    """the human, 2026-10-22: a landing dropped on a red build marks its item rework (tools/queue_mark.py)"""
    try:
        import subprocess as _sp, sys as _sy, pathlib as _pl
        d = r.get('delivery') or {}
        items = [str(d['item'])] if isinstance(d, dict) and d.get('item') else []
        items += [str(c).split()[0] for c in (r.get('changed') or []) if str(c).strip() and '.' in str(c).split()[0]]
        if items:
            root = _pl.Path(__file__).resolve().parent.parent
            _sp.run([_sy.executable, str(root / 'tools' / 'queue_mark.py'), 'rework', str(r.get('stage') or '-'), *items],
                    capture_output=True, timeout=60)
    except Exception:
        pass


def drop_other_writers(b: dict, last: dict, failures: list, log, persist: bool = True, own_only: bool = False) -> bool:
    """Merge queue: a failure no delivery of the batch explains, while landings of other writers (U, PI, PR, the
    maintainer, stage 2) that the build names as possible causes were in it: drop those from the candidate (hard
    restore, one commit) and let the next build verify. True when something was dropped."""
    batch_ids = {e['landing'] for e in b['entries']}
    open_ids = {r['id'] for r in ld.records(ld.REQUESTS)}
    # only a change that can break the failing module: one of its own modules fails, or it changed an interface
    ids = sorted({s['id'] for s in last.get('suspects') or [] if s['id'] in open_ids and s['id'] not in batch_ids
                  and set(s.get('fails') or []) & set(failures)
                  and ((not own_only and s.get('kind') == 'interface') or set(s.get('fails') or []) & set(s.get('modules') or []))})
    if not ids:
        return False
    # 2026-10-21 (the human): the importers of a dropped module go out with it. Lake does not attempt the importers of a
    # failed module, so they are not named as failing; left in the candidate they fail the next build on their import
    # of the dropped file ("bad import"), one layer per build (938-landing build of 993813cbe8: 404 bad imports after
    # 12 restores were dropped alone).
    _recs = {r['id']: r for r in ld.records(ld.REQUESTS)}
    # 2026-10-24: the rework take-out of a red build (tools/red_rework.py, note "red build rework") removes the failing
    # module; dropping it put the module back and the next build failed on it again (13:01, AdicSmoothDualizingComplexes)
    # and the upstream sync's landings (record field `upsync`): dropping one would revert upstream files; a module they
    # break becomes a rework item instead (mechanical_red)
    # and the maintainer's landings (group L: undos of mass quarantines, put-backs, cycle breaks, rework moves): they
    # write thousands of modules; at 21:12 two undos went out as "importers of a dropped module" and 3824 files were
    # reverted, the upstream sync among them
    _rework = {i for i, r in _recs.items() if str(r.get('note') or '').startswith('red build rework') or r.get('upsync')
               or r.get('group') == 'L'}
    ids = [i for i in ids if i not in _rework]
    if not ids:
        return False
    # the import lines of the open landings' own files, read now: the cached library graph predates the restores and
    # missed their importers (11:53-11:57: 218, 68, 34 landings dropped in four builds instead of one)
    _imp_re = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)", re.M)
    _imports = {}
    for _r in _recs.values():
        for _f in _r.get('files') or []:
            _p = li.LEAN / _f['path']
            if _f.get('module') and _p.is_file():
                try:
                    _imports[_f['module']] = set(_imp_re.findall(_p.read_text(errors='replace')))
                except OSError:
                    pass
    _mod_of = {f['module']: r['id'] for r in _recs.values() if r['id'] not in batch_ids
               for f in r.get('files') or [] if f.get('module')}
    _importers = {}
    for _m, _deps in _imports.items():
        for _d in _deps:
            _importers.setdefault(_d, set()).add(_m)
    # only a file the drop removes (one the landing created, e.g. a restore from quarantine) leaves dangling imports;
    # a changed file goes back to the version its importers were compiled against
    _gone = {f['module'] for i in ids if i in _recs for f in _recs[i].get('files') or []
             if f.get('module') and not f.get('existed', True)}
    # a failing module whose file is no longer in the library (taken out in an earlier round) is a removed root too:
    # the modules still importing it fail with "no such file" / "bad import" build after build
    _gone |= {m for m in failures if not (li.LEAN / (m.replace('.', '/') + '.lean')).is_file()}
    _seen, _todo = set(_gone), list(_gone)
    while _todo:
        for _x in _importers.get(_todo.pop(), ()):
            if _x not in _seen:
                _seen.add(_x); _todo.append(_x)
    _extra = sorted({_mod_of[_m] for _m in _seen if _m in _mod_of} - set(ids) - _rework)
    if _extra:
        log(f"red build {last.get('time')}: {len(_extra)} landing(s) whose modules import a dropped module go out with it")
        ids = ids + _extra
    t0 = time.time()
    reason = (f"the global build of {str(last.get('commit'))[:10]} failed in {' '.join(failures[:6])}; this change is a possible cause"
              " (the compiler's full messages: coord/build-errors/<module>.txt in the clone)")
    with md.merge_lock():
        with ld.tree_lock():
            dropped, restore_to, notes = ld.drop_plan(ids)
            lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
            tip = md.git('rev-parse', 'HEAD')
            recovery.commit_inverse(ROOT, {f"{lean_rel}/{rel}": data for rel, data in restore_to.items()}, tip,
                                    f"Drop {len(dropped)} landing(s) from the candidate after the red build of batch {b['id']}")
            ld.drop_close(dropped, reason)
    by_landing = {e['landing']: e for e in b['entries']}
    for r in dropped:
        e = by_landing.get(r['id'])
        if e is not None and e['state'] == 'landed':
            e['state'] = 'returned'; e['why'] = 'taken out with ' + ', '.join(r.get('chained') or ids)
            give_back(e['group'], e['item'], e['head'], reason + '; it changed the same file(s) after a dropped change', log)
        elif r.get('delivery'):
            return_record(r, reason, log)
        log(f"batch {b['id']}: DROPPED from the candidate {r['id']} ({r['group']}: {r.get('note', '')[:100]})")
        _qmark_rework(r)
    for x in notes:
        MQ_LOG('drop: ' + x)
    MQ_LOG(f"red build {last.get('time')}: {len(dropped)} landing(s) of other writers dropped, {len(restore_to)} file(s) restored, "
           f"{time.time() - t0:.1f} s")
    if persist:
        b['await_recovery'] = True
        write_json(OPEN, b)
    return True


def return_record(r: dict, reason: str, log) -> None:
    """A dropped landing that carries its delivery (stage 2, tools/nt_batch2.py) goes back to its group."""
    d = r['delivery']
    give_back(d['group'], d['item'], d.get('head', '?'),
              f"(merge queue) your landing {r['id']} was taken out of the candidate: {reason}"
              + (f"; it changed the same file(s) after {', '.join(r['chained'])}" if r.get('chained') else ''), log)


PARTIAL = BD / "partial-verified.json"


def _ls_tree(commit: str, rel: str) -> dict:
    out = subprocess.run(["git", "ls-tree", "-r", "-z", commit, "--", rel], cwd=ROOT, capture_output=True).stdout.decode()
    res = {}
    for x in out.split("\0"):
        if x:
            meta, path = x.split("\t", 1)
            mode, _, sha = meta.split()
            res[path] = (mode, sha)
    return res


def advance_verified(build_commit: str, included: list[dict], verified: list[dict]) -> str:
    """The verified main after a red build whose clean landings land: the old verified main with the files of the
    verified landings at their own version (staged/), in landing order; every other file the build's landings touched
    stays as it is on the verified main. One commit (no working-tree change), VERIFIED_REF moved to it. Caller holds
    coord/.merge.lock and local/tree.lock."""
    old = md.git("rev-parse", "-q", "--verify", ld.VERIFIED_REF, check=False)
    lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
    base = _ls_tree(old, lean_rel) if old else {}
    built = _ls_tree(build_commit, lean_rel)
    want = {}
    for r in included:
        for f in r.get("files") or []:
            full = f"{lean_rel}/{f['path']}"
            want[full] = base.get(full)
    for r in sorted(verified, key=ld.order_key):
        for f in r["files"]:
            full = f"{lean_rel}/{f['path']}"
            st = ld.STAGED / r["id"] / f["path"]
            if f.get("deleted"):
                want[full] = None
            elif st.is_file():
                sha = subprocess.run(["git", "hash-object", "-w", str(st)], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()
                want[full] = ("100644", sha)
            else:
                want[full] = built.get(full)
    with tempfile.TemporaryDirectory(prefix="sheaf-verified-") as td:
        env = dict(os.environ, GIT_INDEX_FILE=str(pathlib.Path(td) / "index"))
        subprocess.run(["git", "read-tree", old or build_commit], cwd=ROOT, env=env, check=True, capture_output=True)
        info = "".join((f"{v[0]} {v[1]}\t{k}\n" if v else f"0 {'0' * 40}\t{k}\n") for k, v in sorted(want.items()))
        subprocess.run(["git", "update-index", "--index-info"], cwd=ROOT, env=env, input=info, text=True, check=True, capture_output=True)
        tree = subprocess.run(["git", "write-tree"], cwd=ROOT, env=env, check=True, capture_output=True, text=True).stdout.strip()
    msg = (f"Verified main after the red build of {build_commit[:10]}: {len(verified)} landing(s) it compiled cleanly\n\n"
           "tools/batch_land.py land_rest (the human, 2026-10-25: the failures go out, the rest lands from the same build)")
    new = subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit-tree", tree]
                         + (["-p", old] if old else []) + ["-m", msg], cwd=ROOT, check=True, capture_output=True, text=True).stdout.strip()
    subprocess.run(["git", "update-ref", ld.VERIFIED_REF, new] + ([old] if old else []), cwd=ROOT, check=True, capture_output=True)
    return new


RED_HANDLED = ld.B / "red-handled.json"


def land_rest(log) -> int:
    """land_rest, then local/builds/red-handled.json names the red build whose handling is complete: land_rest is the
    last step of every red handling (mechanical_red, round_red, red_without_batch, a batch's later step), and
    ~/cc1/retry_round.py starts the retry only after it (2026-10-25)."""
    last = ld.read_json(ld.B / "last.json") or {}
    try:
        return _land_rest(log)
    finally:
        if last.get("result") == "red":
            write_json(RED_HANDLED, {"time": last.get("time"), "source_fingerprint": last.get("source_fingerprint"), "at": ld.now()})


def _land_rest(log) -> int:
    """2026-10-25 (the human): after a red build has been handled (its failing landings taken out, with the importers
    of their removed files), every landing of that build that compiled cleanly lands from it: none of its modules
    failed or imports a failing module or a module of a landing taken out since (import graph of the build copy,
    local/builds/last-graph.pkl; tools/build.py clean_landings ran its batch checks). They are closed as verified and
    the verified main advances (advance_verified). Each red build once (local/batch/partial-verified.json)."""
    last = ld.read_json(ld.B / "last.json") or {}
    if last.get("result") != "red" or not isinstance(last.get("clean"), list) or not last.get("failing"):
        return 0
    seen = read_json(PARTIAL) or []
    if last.get("time") in seen:
        return 0
    write_json(PARTIAL, (seen + [last.get("time")])[-200:])
    try:
        with open(ld.B / "last-graph.pkl", "rb") as fh:
            saved = pickle.load(fh)
    except Exception as exc:  # noqa: BLE001
        log(f"land_rest: no import graph of the build ({exc!r}); nothing lands from it"[:300]); return 0
    if saved.get("commit") != last.get("commit"):
        log("land_rest: the saved import graph is of another build; nothing lands from it"); return 0
    graph = saved["graph"]
    t0 = time.time()
    with md.merge_lock():
        with ld.tree_lock():
            open_recs = {r["id"]: r for r in ld.records(ld.REQUESTS)}
            inc, out_mods = [], set()
            for i in last.get("included") or []:
                r = open_recs.get(i) or ld.read_json(ld.DONE / f"{i}.json")
                if not r:
                    continue
                inc.append(r)
                if i not in open_recs and r.get("result", "verified") != "verified":
                    out_mods |= {f["module"] for f in r.get("files") or []}
            blocked = set(last["failing"]) | out_mods
            blocked |= li.downstream(blocked, graph)
            ok = [open_recs[i] for i in last["clean"] if i in open_recs
                  and not ({f["module"] for f in open_recs[i]["files"]} & blocked)]
            # 2026-10-27 (red build 14:46:31Z of 6db8f8a0f6): a landing whose file is no longer in lean/ (moved to
            # quarantine/ or taken out after it landed; 11828f6cc28 moved 2747 restored modules out before that build) did
            # not compile in this build: its file was not in the copy. Landed from it, its staged version went into the
            # verified main and came back into the next candidate without its quarantined imports (retry 1: ~3000 "no
            # such file" / "bad import"). It does not land; it stays open and waits for its file.
            gone = [r for r in ok if any(not f.get("deleted") and f.get("module") and not (li.LEAN / f["path"]).is_file()
                                         for f in r["files"])]
            if gone:
                log(f"land_rest: {len(gone)} clean landing(s) not landed, their file is no longer in lean/ (quarantined or "
                    f"taken out since): {' '.join(r['id'] for r in gone[:6])}")
                ok = [r for r in ok if r not in gone]
            # 2026-10-25 (the human): a landing that broke an importer (importer_blame) does not land; the red handling
            # takes it out
            try:
                blamed = {i for x in importer_blame(last, graph).values() for i in x["ids"]}
            except Exception as exc:  # noqa: BLE001
                log(f"land_rest: importer blame failed ({exc!r}); nothing lands from it"[:300]); return 0
            if blamed & {r["id"] for r in ok}:
                log(f"land_rest: not landed, they broke an importer: {' '.join(sorted(blamed & {r['id'] for r in ok}))}")
                ok = [r for r in ok if r["id"] not in blamed]
            if not ok:
                log(f"land_rest: red build {last.get('time')}: nothing lands from it ({len(last['clean'])} clean, all blocked or closed)")
                return 0
            new = advance_verified(last["commit"], inc, ok)
            for r in ok:
                r = dict(r)
                r.update(result="verified", commit=last["commit"], closed=ld.now(), partial_of=last.get("time"))
                ld.write_json(ld.DONE / f"{r['id']}.json", r)
                (ld.REQUESTS / f"{r['id']}.json").unlink(missing_ok=True)
                shutil.rmtree(ld.BACKUP / r["id"], ignore_errors=True)
                shutil.rmtree(ld.STAGED / r["id"], ignore_errors=True)
    _mark_landed(ok)
    log(f"land_rest: red build {last.get('time')} ({str(last.get('commit'))[:10]}): {len(ok)} of {len(last.get('included') or [])} "
        f"landing(s) compiled cleanly and land from it; {len(out_mods)} module(s) of taken-out landings, {len(last['failing'])} "
        f"failing; verified main -> {new[:10]} ({time.time() - t0:.0f} s)")
    MQ_LOG(f"land_rest: {len(ok)} landing(s) of the red build {last.get('time')} verified; verified main {new[:10]}")
    return len(ok)


def _qmark_at_landing(stage: str, item: str, landing=None) -> None:
    """The human, 2026-10-25: a delivery leaves the queue the moment it lands (its commit is on live), so a finished item
    is never dispatched again (C6's FiniteCtfInternalEtaleRealization was taken again 34 s after its landing, the queue
    write then in progress had read the tree before it). tools/queue_mark.py done removes the item's row at once; a
    stage-3 module that keeps a `sorry` is marked `landed` and stays listed. A red build that takes the landing out
    marks it rework (_qmark_rework) and the next queue write lists it again. Never fails the caller."""
    try:
        subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "done", stage, item,
                        "--note", f"landed {landing or '-'}"], cwd=ROOT, capture_output=True, timeout=60)
    except Exception:  # noqa: BLE001
        pass


def _mark_landed(recs) -> None:
    """tools/queue_mark.py done for the items of the landings verified (as tools/build.py _mark_verified)."""
    by_stage = {}
    for r in recs:
        st = str(r.get("stage") or "-")
        d = r.get("delivery") or {}
        if isinstance(d, dict) and d.get("item") and "." not in str(d.get("item")):
            by_stage.setdefault(st, set()).add(str(d["item"]))
        for c in r.get("changed") or []:
            mod = str(c).split()[0] if str(c).strip() else ""
            if mod and "." in mod:
                by_stage.setdefault("3" if st == "-" else st, set()).add(mod)
    for st, items in by_stage.items():
        try:
            subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "done", st, *sorted(items)],
                           cwd=ROOT, capture_output=True, timeout=300)
        except Exception:  # noqa: BLE001
            pass


def _sync_running() -> bool:
    """2026-10-21 (the human): a scheduled upstream sync (~/cc1/upsync-quick.py) no longer stops the lander; while its
    marker exists the lander lands but leaves red builds to the sync's own quarantine rounds."""
    return (ROOT / "local" / "UPSYNC_RUNNING").exists()


RETRY_ROUND = ld.B / "retry-round.json"


def retry_round_open() -> bool:
    """2026-10-25 (the human: each build round is finished on its own): ~/cc1/retry_round.py retries a red build on the
    same snapshot until it is green (local/builds/retry-round.json). Meanwhile no new batch lands: a red retry must
    find the landings it contains still open here, and the new batch waits for the next round anyway. A file left by
    a build loop that is no longer running holds nothing."""
    if not RETRY_ROUND.exists():
        return False
    try:
        pid = int((pathlib.Path.home() / "cc1" / "buildloop.pid").read_text().split()[0])
        return b"buildloop.sh" in pathlib.Path(f"/proc/{pid}/cmdline").read_bytes()
    except (OSError, ValueError, IndexError):
        return False


# ---------------------------------------------------------------- a landing that breaks an importer
# 2026-10-25 (the human: a red round only removes what caused the failures, and must always be able to finish): a
# failing module that no landing of the build wrote was broken by a landing that changed a module in its import
# closure (A9's ProEtaleSectionModuleFunctors removed upperStar_tensorπ_delta, used by SectionOrdinaryOplaxNormalization;
# G5's ProEtaleFiniteClopenTensorCalculus left FiniteClopenConstructibilityBounds stuck at a universe constraint).
# Those landings are blamed: land_rest does not land them, the red handling takes them out and returns them to their
# writers. Quarantine (tools/red_rework.py) is only for a failure no landing explains.

_IDENT = re.compile(r"[\w'.!?]+")
_UNKNOWN = re.compile(r"[Uu]nknown (?:identifier|constant|declaration) [`'‘«]?([^`'’»\s]+)")


def _git_text(commit: str, rel: str) -> str | None:
    if not commit:
        return None
    lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
    r = subprocess.run(["git", "show", f"{commit}:{lean_rel}/{rel}"], cwd=ROOT, capture_output=True)
    return r.stdout.decode(errors="ignore") if r.returncode == 0 else None


def _blame_records(last: dict, published: dict) -> list[dict]:
    """The landings of the snapshot: those the build included (open or verified), and those land_rest verified from a
    red build since the last green one (they are in the snapshot but no longer in `included`)."""
    out, seen = [], set()
    for i in last.get("included") or []:
        r = ld.read_json(ld.REQUESTS / f"{i}.json") or ld.read_json(ld.DONE / f"{i}.json")
        if r:       # a landing taken out since stays blamed (land_rest after the take-out lands the others)
            out.append(r); seen.add(i)
    t = str(published.get("time") or "")
    if t:
        lo = time.strftime("%Y%m%dT%H%M%S", time.gmtime(calendar.timegm(time.strptime(t, "%Y-%m-%dT%H:%M:%SZ")) - 2 * 86400))
        for p in sorted(ld.DONE.glob("*.json")):
            if p.name[:15] < lo or p.stem in seen:
                continue
            r = ld.read_json(p)
            if r and r.get("result") == "verified" and str(r.get("partial_of") or "") > t:
                out.append(r); seen.add(r["id"])
    return out


def importer_blame(last: dict, graph: dict | None = None, failing=None, published: dict | None = None) -> dict:
    """{failing module: {'ids': [landing ids blamed], 'by': 'unknown name' | 'name' | 'closest', 'names': [...], 'dist': n,
    'others': [other landings in its closure]}} for each failing module that no landing of the snapshot wrote and whose
    import closure a landing of the snapshot changed. Blamed: the landings whose changed interface (`changed`, or a
    declaration their file no longer has, private ones included) removes or renames a name the failing module uses or
    the compiler calls unknown (those alone when there are such); failing that, the landings closest to it in the
    import graph."""
    failing = list(failing if failing is not None else
                   dict.fromkeys(list(last.get("failing") or []) + [c["module"] for c in last.get("batch_checks") or []]))
    if not failing:
        return {}
    if published is None:
        published = ld.read_json(ld.B / "published.json") or {}
    if graph is None:
        try:
            with open(ld.B / "last-graph.pkl", "rb") as fh:
                saved = pickle.load(fh)
            graph = saved["graph"] if saved.get("commit") == last.get("commit") else None
        except Exception:  # noqa: BLE001
            graph = None
        if graph is None:
            graph = library_imports()
    recs = _blame_records(last, published)
    written = {f.get("module") for r in recs for f in r.get("files") or []}
    memo, out, texts = {}, {}, {}
    for m in failing:
        if m in written or not li.file_of(m).is_file():
            continue
        below = li.closure(m, graph, memo)
        cands = [r for r in recs if {f.get("module") for f in r.get("files") or []} & below]
        if not cands:
            continue
        src = li.strip(li.file_of(m).read_text(errors="ignore"))
        used = set()
        for tok in _IDENT.findall(src):
            used.add(tok)
            parts = tok.split(".")
            used |= {".".join(parts[k:]) for k in range(1, len(parts))}
        ep = ROOT / "coord" / "build-errors" / f"{m}.txt"
        err = ep.read_text(errors="ignore") if ep.is_file() else "\n".join(last.get("errors") or [])
        unknown = {x.strip("`'.") for x in _UNKNOWN.findall(err)}

        def sfx(name):
            parts = name.split(".")
            return {".".join(parts[k:]) for k in range(len(parts))}

        def hit(name):
            return name in used or any(len(s) > 3 and s in used for s in sfx(name) - {name})

        named, unknown_hit = {}, {}
        for r in cands:
            names = {str(c).split()[0] for c in r.get("changed") or [] if str(c).strip() and not str(c).startswith("(")}
            for f in r.get("files") or []:
                if f.get("module") not in below:
                    continue
                key_ = (r["id"], f["path"])
                if key_ not in texts:
                    st, bk = ld.STAGED / r["id"] / f["path"], ld.BACKUP / r["id"] / f["path"]
                    new = st.read_text(errors="ignore") if st.is_file() else _git_text(last.get("commit"), f["path"])
                    old = bk.read_text(errors="ignore") if bk.is_file() else _git_text(published.get("commit"), f["path"])
                    texts[key_] = (old, new)
                old, new = texts[key_]
                if old is not None and new is not None:
                    gone = {c["name"] for c in li.commands(old) if c["name"]} - {c["name"] for c in li.commands(new) if c["name"]}
                    names |= gone
            u = sorted(n for n in names if sfx(n) & unknown)
            if u:
                unknown_hit[r["id"]] = u
            h = sorted(n for n in names if hit(n))
            if h:
                named[r["id"]] = h
        # distance from the failing module down its imports to each landing's modules
        dist, frontier, d = {}, [m], 0
        seen = {m}
        while frontier:
            d += 1
            nxt = []
            for x in frontier:
                for y in graph.get(x, ()):
                    if y not in seen:
                        seen.add(y); dist[y] = d; nxt.append(y)
            frontier = nxt
        rd = {r["id"]: min(dist.get(f.get("module"), 10**6) for f in r.get("files") or []) for r in cands}
        if unknown_hit:     # a name the compiler calls unknown, removed or renamed by the landing: that landing alone
            named = unknown_hit
            ids, by = sorted(named, key=lambda i: (rd[i], i)), "unknown name"
        else:
            # 2026-10-26 (the human: no guessing; a failing module no landing wrote goes to rework with its importers):
            # only a landing that removed or renamed a name the compiler calls unknown is blamed. A name the module merely
            # uses, or the landing closest in the import graph, was a guess (a 172-landing round took out 88 landings in
            # two 70-minute retries and kept failing on the same two modules).
            continue
        out[m] = {"ids": ids, "by": by, "names": sorted({n for i in ids for n in named.get(i, [])})[:8],
                  "dist": min(rd[i] for i in ids), "others": sorted(set(rd) - set(ids))}
    return out


def take_out_blamed(last: dict, blame: dict, log, where: str, skip=()) -> bool:
    """Take the blamed landings out (their files back to the version before them) and return them to their writers.
    Open landings: as drop_other_writers (ld.drop_plan). Landings land_rest verified since the last green build: their
    files back to the last green build's version, one maintainer landing (group M) that the next build verifies, the
    record closed as reverted. `skip`: ids the caller returns another way (a batch's own deliveries). True when
    something was taken out."""
    reasons = {}
    for m, x in blame.items():
        for i in x["ids"]:
            why = (f"the global build of {str(last.get('commit'))[:10]} failed in {m}, which imports your module(s)"
                   + (f" and uses {', '.join(x['names'][:4])}, which your landing removed or changed" if x["names"] else
                      " (yours is the closest change below it)")
                   + f"; adapt the change so that {m} still compiles, or adapt {m} too, and deliver again"
                     " (the compiler's full messages: coord/build-errors/<module>.txt in the clone)")
            reasons[i] = reasons.get(i, why)
    ids = sorted(set(reasons) - set(skip))
    if not ids:
        return False
    open_ids = {r["id"] for r in ld.records(ld.REQUESTS)}
    lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
    removed = False
    opened = [i for i in ids if i in open_ids]
    if opened:
        try:
            with md.merge_lock():
                with ld.tree_lock():
                    dropped, restore_to, notes = ld.drop_plan(opened)
                    recovery.commit_inverse(ROOT, {f"{lean_rel}/{rel}": data for rel, data in restore_to.items()},
                                            md.git('rev-parse', 'HEAD'),
                                            f"Take out {len(dropped)} landing(s) that broke an importer ({where}, red build {last.get('time')})")
                    ld.drop_close(dropped, "it broke an importer in the global build", reasons)
        except Exception as x:  # noqa: BLE001
            log(f"{where}: take-out of the landings that broke an importer failed ({x!r}); retried on the next red"[:400])
            dropped, notes = [], []
        for r in dropped:
            if r.get("delivery"):
                return_record(r, reasons.get(r["id"]) or "it changed the same file(s) after a landing that broke an importer", log)
            _qmark_rework(r)
            log(f"{where}: TAKEN OUT {r['id']} ({r['group']}: {(r.get('note') or ' '.join(f['module'] for f in r['files']))[:100]}): broke an importer")
        for x in notes:
            MQ_LOG("blame drop: " + x)
        removed = removed or bool(dropped)
    closed = [ld.read_json(ld.DONE / f"{i}.json") for i in ids if i not in open_ids]
    closed = [r for r in closed if r and r.get("result") == "verified"]
    pub = (ld.read_json(ld.B / "published.json") or {}).get("commit")
    busy = {f["path"] for r in ld.records(ld.REQUESTS) for f in r.get("files") or []}
    # a file another verified landing changed since the last green build too: going back would undo that one as well
    busy |= {f["path"] for r in _blame_records(last, ld.read_json(ld.B / "published.json") or {}) if r["id"] not in ids
             for f in r.get("files") or []}
    restore, undone = {}, []
    for r in closed:
        old = {f["path"]: _git_text(pub, f["path"]) for f in r.get("files") or []}
        if any(v is None for v in old.values()) or set(old) & busy:
            log(f"{where}: {r['id']} broke an importer but cannot be undone here (a file new since the last green build, "
                "or another landing changed it since); the maintainer decides")
            continue
        restore.update(old); undone.append(r)
    if undone:
        try:
            with md.merge_lock():
                with ld.tree_lock():
                    before = {rel: (li.LEAN / rel).read_bytes() if (li.LEAN / rel).is_file() else None for rel in restore}
                    recovery.commit_inverse(ROOT, {f"{lean_rel}/{rel}": t.encode() for rel, t in restore.items()},
                                            md.git('rev-parse', 'HEAD'),
                                            f"Undo {len(undone)} landing(s) that broke an importer ({where}, red build "
                                            f"{last.get('time')}): back to the last green build's version")
                    prev = {rel: b for rel, b in before.items() if b is not None and b != restore[rel].encode()}
                    rec = ld.new_record("M", prev, f"maintainer (tools/batch_land.py take_out_blamed): undo "
                                        f"{', '.join(r['id'] for r in undone)}; they broke an importer; back to the last "
                                        "green build's version") if prev else None
                    for r in undone:
                        r = dict(r)
                        r.update(result="reverted", reason=reasons[r["id"]], closed=ld.now(), undone_by=(rec or {}).get("id"))
                        ld.write_json(ld.DONE / f"{r['id']}.json", r)
        except Exception as x:  # noqa: BLE001
            log(f"{where}: undo of verified landings that broke an importer failed ({x!r})"[:400])
            undone = []
        for r in undone:
            if r.get("delivery"):
                return_record(r, reasons[r["id"]], log)
            _qmark_rework(r)
            log(f"{where}: UNDONE {r['id']} ({r['group']}, verified from a red build since the last green one): broke an importer")
        removed = removed or bool(undone)
    return removed


def blame_out(last: dict, orphan: list, log, where: str, skip=()) -> tuple[dict, bool]:
    """The failing modules no landing wrote: blame (importer_blame) and take out (take_out_blamed). Returns (blame,
    removed); the modules in `blame` are not for quarantine."""
    try:
        blame = importer_blame(last, failing=orphan)
    except Exception as x:  # noqa: BLE001
        log(f"{where}: importer blame failed ({x!r})"[:300]); return {}, False
    # 2026-10-25 (the human: remove only what caused the errors): a big maintainer/sync landing (group M or L, an
    # upstream sync, or SHEAF_BLAME_BIG_FILES+ files) is not taken out for an importer it broke; the failing importer
    # stays an orphan and becomes a rework item. Retry 1 of 2026-10-25 took out the 170-file import narrowing
    # 20261025T073601-M-1709494-79 for two importers, and retry 2 rebuilt ~1400 modules.
    big_n = int(os.environ.get('SHEAF_BLAME_BIG_FILES', '20'))

    def _big(i):
        r = ld.read_json(ld.REQUESTS / f"{i}.json") or ld.read_json(ld.DONE / f"{i}.json") or {}
        return not r.get('delivery') and (r.get('group') in ('M', 'L') or bool(r.get('upsync'))
                                          or len(r.get('files') or []) >= big_n)
    for m in list(blame):
        if all(_big(i) for i in blame[m]['ids']):
            log(f"{where}: {m} broken by big landing(s) {', '.join(blame[m]['ids'])}; kept, {m} goes to rework")
            del blame[m]
    for m, x in blame.items():
        log(f"{where}: {m} broken by {', '.join(x['ids'])} ({x['by']}" + (f": {', '.join(x['names'][:4])}" if x['names'] else
            f", {x['dist']} import(s) below") + f"; {len(x['others'])} other landing(s) in its closure kept)")
    return blame, (take_out_blamed(last, blame, log, where, skip) if blame else False)


def round_red(last: dict, log) -> bool:
    """A red build of a retry round with no batch open, by the mechanical rule (mechanical_red): a failing module that
    a landing of the build wrote goes out with that landing (and the importers of its removed files); a failing module
    no landing took out becomes a rework item (tools/red_rework.py moves it and its importers to quarantine/; refused
    when it would reach the target statements or move too many modules: then nothing is taken out for it). Then the
    clean landings land (land_rest). True when something was taken out."""
    failing = list(dict.fromkeys(list(last.get('failing') or []) + [c['module'] for c in last.get('batch_checks') or []]))
    removed = drop_other_writers({'id': '-', 'entries': []}, last, failing, log, persist=False, own_only=True)
    # a batch delivery (group L, record with `delivery`; drop_other_writers never drops group L) whose own module fails
    # goes back to its group, as mechanical_red returns it while its batch is open
    inc = set(last.get('included') or [])
    ids = sorted(r['id'] for r in ld.records(ld.REQUESTS) if r['id'] in inc and r.get('delivery')
                 and {f.get('module') for f in r.get('files') or []} & set(failing))
    if ids:
        reason = (f"the global build of {str(last.get('commit'))[:10]} (retry round) failed in your module(s) "
                  f"{' '.join(sorted({f.get('module') for i in ids for f in ld.read_json(ld.REQUESTS / f'{i}.json')['files']} & set(failing))[:6])}"
                  "; fix and deliver again (the compiler's full messages: coord/build-errors/<module>.txt)")
        with md.merge_lock():
            with ld.tree_lock():
                dropped, restore_to, notes = ld.drop_plan(ids)
                lean_rel = li.LEAN.resolve().relative_to(ROOT.resolve()).as_posix()
                recovery.commit_inverse(ROOT, {f"{lean_rel}/{rel}": data for rel, data in restore_to.items()},
                                        md.git('rev-parse', 'HEAD'),
                                        f"Drop {len(dropped)} landing(s) whose module failed in the retry round of {last.get('time')}")
                ld.drop_close(dropped, reason)
        for r in dropped:
            if r.get('delivery'):
                return_record(r, reason, log)
            _qmark_rework(r)
            log(f"retry round: DROPPED {r['id']} ({r['group']}: {r.get('note', '')[:100]})")
        for x in notes:
            MQ_LOG('drop: ' + x)
        removed = removed or bool(dropped)
    out_mods = set()
    for i in last.get('included') or []:
        r = ld.read_json(ld.DONE / f"{i}.json")
        if r and r.get('result') == 'reverted':
            out_mods |= {f.get('module') for f in r.get('files') or []}
    text = (ld.LOCAL / 'build.log').read_text(errors='ignore') if (ld.LOCAL / 'build.log').exists() else ''
    blocks = log_blocks(text)
    messages = {m: blocks.get(m) or '\n'.join(last.get('errors') or []) for m in failing}
    messages.update({c['module']: c['message'] for c in last.get('batch_checks') or []})
    def _stale_bad_import(m):
        errs = [l for l in (messages.get(m) or '').splitlines() if l.lstrip().startswith('error')]
        bad = [re.search(r"bad import '([^']+)'", l) for l in errs]
        return bool(errs) and all(bad) and all(li.file_of(x.group(1)).is_file() for x in bad)
    orphan = [m for m in failing if m not in out_mods and li.file_of(m).is_file() and not _stale_bad_import(m)]
    if orphan:
        try:
            rid, fixed = red_rework.add_suggested_imports(orphan, messages)
        except Exception as x:  # noqa: BLE001
            rid, fixed = '', []; log(f"retry round: adding the suggested imports failed: {x!r}"[:300])
        if fixed:
            removed = True
            log(f"retry round: added the public imports the compiler named to {len(fixed)} module(s) (landing {rid}): {' '.join(fixed[:8])}")
            orphan = [m for m in orphan if m not in fixed]
    if orphan:
        # 2026-10-25 (the human): a failing module no landing wrote, below which a landing of the snapshot changed a
        # module: that landing goes out (importer_blame); quarantine only for a failure no landing explains
        blame, out = blame_out(last, orphan, log, 'retry round')
        removed = removed or out
        # 2026-10-25 (the human): a culprit that cannot be undone (take_out_blamed: a file new since the last green
        # build, or changed by another landing since) does not stop the round: the failing module stays an orphan and
        # goes to rework/quarantine below. Taken out = its record closed as reverted.
        def _out(i):
            return (ld.read_json(ld.DONE / f"{i}.json") or {}).get('result') == 'reverted'
        for m in [m for m in orphan if m in blame and not any(_out(i) for i in blame[m]['ids'])]:
            log(f"retry round: {m}: no culprit of it could be taken out ({', '.join(blame[m]['ids'])}); {m} goes to rework")
            del blame[m]
        orphan = [m for m in orphan if m not in blame]
    if orphan:
        errs = red_rework.first_errors(orphan)
        causes = {m: errs.get(m) or messages.get(m, '')[:1500] or 'error: failed in the global build' for m in orphan}
        # all together, or, when that is refused, each alone: a module whose move is refused does not keep the others
        for group in [orphan] + ([[m] for m in orphan] if len(orphan) > 1 else []):
            try:
                rid, moved = red_rework.quarantine(set(group), causes, f"retry round of the red build {last.get('time')}")
            except red_rework.Refuse as x:
                # nothing is guessed (no landing that did not write the module is dropped): the failure stays, the
                # retry has the same sources and ~/cc1/retry_round.py stops for the maintainer
                log(f"retry round: rework move of {' '.join(group[:6])} refused ({x})")
                if len(group) == 1 or len(orphan) == 1:
                    alert(None, ' '.join(group[:6]), f'retry round: rework move refused ({x})'[:200], 'fix the failing module (coord/build-errors)')
                continue
            removed = removed or bool(moved)
            log(f"retry round: {len(group)} failing module(s) no landing wrote -> rework, {len(moved)} module(s) moved to "
                f"quarantine/ (landing {rid or '-'}): {' '.join(group[:8])}")
            if group is orphan:
                break
    # 2026-10-26: a module failing with "bad import"/"no such file" because a module it imports is gone from lean/ (a
    # take-out left it): it and its importers go to quarantine/ as rework (tools/red_rework.py sweep). The round took
    # nothing out for it and the retry loop STOPPED on the same sources (21:09-21:20, UniformConstructibleExt).
    try:
        _when = last.get("time")
        rid, moved = red_rework.sweep(f"retry round of the red build {_when}: importers of modules gone from lean/")
        if moved:
            removed = True
            log(f"retry round: {len(moved)} module(s) importing modules gone from lean/ moved to quarantine/ "
                f"(landing {rid or '-'}): {' '.join(moved[:8])}")
    except Exception as x:  # noqa: BLE001
        log(f"retry round: sweep of importers of modules gone from lean/ failed ({x!r})"[:400])
    land_rest(log)
    write_json(RED_HANDLED, {"time": last.get("time"), "source_fingerprint": last.get("source_fingerprint"), "at": ld.now(),
                             "round_red": True, "removed": bool(removed)})
    return removed


def red_without_batch(log) -> bool:
    """Merge queue: a red build with no batch open (only other writers' landings in it) is handled here: the landings
    the build names are dropped from the candidate. Each red result is handled once (local/batch/mq-red.json)."""
    last = ld.read_json(ld.B / 'last.json') or {}
    if last.get('result') != 'red':
        return False
    seen_p = BD / 'mq-red.json'
    seen = read_json(seen_p) or []
    if last.get('time') in seen or (last.get('source_fingerprint') and last['source_fingerprint'] in seen):
        return False
    seen = (seen + [last.get('time'), last.get('source_fingerprint')])[-200:]
    write_json(seen_p, seen)
    log(f"RED build {last.get('time')} with no batch open; failing {' '.join((last.get('failing') or [])[:8])}")
    if retry_round_open():
        return round_red(last, log)
    if drop_other_writers({'id': '-', 'entries': []}, last, list(last.get('failing') or []), log, persist=False):
        land_rest(log)
        return True
    if blame_out(last, list(last.get('failing') or []), log, 'red build')[1]:      # 2026-10-25: importer_blame
        land_rest(log)
        return True
    alert(None, ' '.join(last.get('failing') or []), 'red build with no batch open and no droppable landing', 'maintainer diagnosis')
    land_rest(log)
    return False


def closure_fallback(b, last, log, imports=None):
    """Alert and defer all closure-touching deliveries; leave independent work in place."""
    failures = list(last.get('failing') or []) + [c['module'] for c in last.get('batch_checks') or []]
    alert(b['id'], ' '.join(failures) or '?', 'no suspect or four recovery rounds', 'repair failing import closure')
    if imports is None: imports = library_imports()
    closure = set()
    for m in failures: closure |= li.closure(m, imports, {}) | {m}
    # At the no-suspect boundary, independently attributed failures still
    # return their suspects, in the same transaction as deferred closures.
    T = triage(b, last, imports) if b['round'] < ROUNDS else {'decisions': [], 'open': []}
    decisions = T['decisions'] + verdict_decisions({'open': T['open']}, None)
    execute(b, decisions, log, deferred=closure, imports=imports)
    b['fallback'] = True
    write_json(OPEN, b)
    chosen = [e for e in b['entries'] if e['state'] == 'waiting']
    log(f"batch {b['id']}: ALERT; {len(chosen)} closure deliveries waiting; build remaining tree")


def seen_red(b: dict, last: dict) -> bool:
    """This red result was handled already: the same build, or build.py's cached result for a source tree already
    handled (2026-10-19: a cached red rewrites last.json with a new time and the same failure was handed to triage
    again)."""
    fp = last.get("source_fingerprint")
    return last.get("time") in b["handled"] or bool(fp and fp in b.get("handled_sources", []))


def pipeline_on() -> bool:
    """SHEAF_PIPELINE_BATCHES=1 in coord/sheaf.env, read from the file on every step (not from the environment the
    lander started with), so that switching it off takes effect at once."""
    val = None
    try:
        for line in (ROOT / "coord" / "sheaf.env").read_text().splitlines():
            f = line.split("#", 1)[0].strip()
            if f.startswith("SHEAF_PIPELINE_BATCHES="):
                val = f.split("=", 1)[1].strip().strip("\"'")
    except OSError:
        return False
    return val == "1"


def running_build() -> dict | None:
    """local/builds/current.json of the global build running now (tools/build.py writes it after its snapshot), or None."""
    cur = ld.read_json(ld.B / "current.json")
    if not cur or cur.get("finished"):
        return None
    try:
        cmd = pathlib.Path(f"/proc/{int(cur.get('pid'))}/cmdline").read_bytes()
    except (OSError, TypeError, ValueError):
        return None
    return cur if b"build.py" in cmd else None


def sync_states(b: dict, log) -> None:
    """The landed entries whose landing record the build or a take-out closed: verified, or reverted."""
    for e in b["entries"]:
        if e.get("stage") == "2" and e["state"] in ("returned", "reverted"):
            s2b.mark_out(e)
        if e["state"] != "landed":
            continue
        r = ld.read_json(ld.DONE / f"{e['landing']}.json")
        if r and r.get("result", "verified") == "verified":
            e["state"] = "verified"; e["build"] = r.get("commit")
        elif r:
            e["state"] = "reverted"; e["why"] = r.get("reason")
            log("reverted by the maintainer", e["group"], e["item"], e["head"][:9], "|", str(r.get("reason"))[:200])


def fold_next(b: dict, log) -> dict:
    """The pipelined batch joins the open one (a red build the open batch must handle): one open batch again."""
    nx = read_json(NEXT)
    if not nx:
        return b
    have = {e["landing"] for e in b["entries"]}
    add = [e for e in nx["entries"] if e["landing"] not in have]
    b["entries"] += add
    b.setdefault("folded", []).append(nx["id"])
    for k in ("handled", "handled_sources"):
        if nx.get(k):
            b[k] = list(dict.fromkeys(list(b.get(k) or []) + nx[k]))
    write_json(OPEN, b)
    NEXT.unlink(missing_ok=True)
    log(f"batch {b['id']}: the pipelined batch {nx['id']} ({len(add)} landing(s)) is folded into it for the recovery")
    return b


def maybe_pipeline(b: dict, cache: dict, log) -> str | None:
    """Land the next batch now, while the build of the open one runs (see NEXT); 'landed' or None."""
    if not pipeline_on() or NEXT.exists() or (BD / "landing.json").exists() or (BD / "proof-imports.json").exists():
        return None
    if b.get("await_recovery") or b.get("triage") or b.get("fallback"):
        return None
    cur = running_build()
    if not cur or not cur.get("has_interface") or cur.get("mode"):
        return None
    mine = {e["landing"] for e in b["entries"] if e["state"] == "landed"}
    if not mine or not mine <= set(cur.get("included") or []):
        return None
    return "landed" if land_batch(cache, log, target=NEXT) else None


def mechanical_red(b: dict, last: dict, log, imports) -> str | None:
    """2026-10-24 (the human: "哪个文件报错了就汇报给编辑过这个的worker，如果没有就单独把文件的这个报错作为一个新的返工任务。
    为什么会猜？"): a red build is handled without attribution and without the triage agent. Every failing module that a
    delivery of the build wrote goes back to that delivery with the compiler's message (taken out, as before); every
    failing module no delivery wrote becomes a rework item with its error (tools/red_rework.py: moved to quarantine/
    with its importers, a row in coord/rework.tsv, the worker adapts it). The guessing triage had returned 48
    innocent deliveries in four rounds (BoundaryWeights, 10-24 03:44-05:48) while the failure stayed. Returns None when
    a failure reaches the six target statements (the old handling then decides)."""
    entries = [e for e in b['entries'] if e['state'] == 'landed']
    inc = set(last.get('included') or [])
    if inc and any(e['landing'] in inc for e in entries):
        entries = [e for e in entries if e['landing'] in inc]
    failures = list(dict.fromkeys(list(last.get('failing') or []) +
                                  [c['module'] for c in last.get('batch_checks') or []]))
    if not failures:
        return None
    text = (ld.LOCAL / 'build.log').read_text(errors='ignore') if (ld.LOCAL / 'build.log').exists() else ''
    # 2026-10-24: an import cycle fails every module on it and all their importers (356 at once). Break it first
    # (tools/import_cycle_breaker.py: an upstream module importing ours goes back to upstream's text, our proof is kept
    # for its worker); the next build decides the rest. Nothing is moved to rework for a cycle that was broken.
    if 'build cycle detected' in text:
        try:
            r = subprocess.run([sys.executable, str(ROOT / 'tools' / 'import_cycle_breaker.py')], cwd=ROOT,
                               capture_output=True, text=True, timeout=1800)
            out = (r.stdout or '').strip()
        except Exception as x:  # noqa: BLE001
            out = 'error ' + repr(x)[:200]
        log(f"batch {b['id']}: import cycle in the red build; tools/import_cycle_breaker.py: {out[:400] or 'nothing to break'}")
        if 'broken:' in out:
            b['round'] += 1
            b['await_recovery'] = True
            write_json(OPEN, b)
            return 'returned'
    blocks = log_blocks(text)
    messages = {m: blocks.get(m) or '\n'.join(last.get('errors') or []) for m in failures}
    messages.update({c['module']: c['message'] for c in last.get('batch_checks') or []})
    decisions, orphan = [], []
    for m in failures:
        ws = [e for e in entries if m in (e.get('modules') or [])]
        if ws:
            decisions.append({'failure': m, 'case': 'own-fault', 'return': [key(e) for e in ws], 'by': 'tools',
                              'reason': f'the global build failed in {m}, which your delivery wrote; fix it and deliver again',
                              'message': messages.get(m, '')})
        else:
            orphan.append(m)
    # 2026-10-24: a failure that is only "bad import 'X'" while X is in the library again (taken out and put back since
    # that build, e.g. a rework move undone) says nothing about the module: the next build decides. 52 modules and 33
    # importers were moved to rework at 14:52 for imports a 14:50 undo had already restored.
    def _stale_bad_import(m):
        errs = [l for l in (messages.get(m) or '').splitlines() if l.lstrip().startswith('error')]
        bad = [re.search(r"bad import '([^']+)'", l) for l in errs]
        return bool(errs) and all(bad) and all(li.file_of(x.group(1)).is_file() for x in bad)
    stale = [m for m in orphan if li.file_of(m).is_file() and _stale_bad_import(m)]
    if stale:
        log(f"batch {b['id']}: {len(stale)} module(s) failed only on imports that are back in the library; the next "
            f"build decides, no rework item: {' '.join(stale[:8])}")
        orphan = [m for m in orphan if m not in stale]
    gone = [m for m in orphan if not li.file_of(m).is_file()]
    if gone:   # its landing (another writer's) was taken out already (drop_other_writers): nothing left to rework
        log(f"batch {b['id']}: {' '.join(gone[:8])}: no longer in the library (taken out with its landing); no rework item")
        orphan = [m for m in orphan if m not in gone]
    if not orphan and not decisions:
        b['round'] += 1
        b['await_recovery'] = True
        write_json(OPEN, b)
        return 'returned'
    if orphan:
        try:
            rid, fixed = red_rework.add_suggested_imports(orphan, messages)
        except Exception as x:  # noqa: BLE001
            rid, fixed = "", []; log(f"batch {b['id']}: adding the suggested imports failed: {x!r}"[:300])
        if fixed:
            log(f"batch {b['id']}: added the public imports the compiler named to {len(fixed)} module(s) (landing {rid}): "
                f"{' '.join(fixed[:8])}")
            orphan = [m for m in orphan if m not in fixed]
    if orphan:
        # 2026-10-25 (the human): a failing module no delivery wrote, broken by a landing of the snapshot that changed a
        # module below it (importer_blame): a delivery of this batch goes back to its writer (decision), another
        # writer's landing is taken out (take_out_blamed); quarantine only for a failure no landing explains
        by_id = {e['landing']: e for e in entries}
        blame, _ = blame_out(last, orphan, log, f"batch {b['id']}", skip=set(by_id))
        for m, x in blame.items():
            own = [key(by_id[i]) for i in x['ids'] if i in by_id]
            if own:
                decisions.append({'failure': m, 'case': 'broke-importer', 'return': own, 'by': 'tools',
                                  'reason': (f"the global build failed in {m}, which imports your module(s)"
                                             + (f" and uses {', '.join(x['names'][:4])}, which your delivery removed or changed"
                                                if x['names'] else " (yours is the closest change below it)")),
                                  'message': messages.get(m, '')})
        orphan = [m for m in orphan if m not in blame]
    if orphan:
        errs = red_rework.first_errors(orphan)
        causes = {}
        for m in orphan:
            below = li.closure(m, imports, {})
            ch = [key(e) for e in entries if set(e.get('modules') or []) & below]
            upn = [r['id'] for r in ld.records(ld.REQUESTS) if r.get('upsync')
                   and any(f.get('module') in below | {m} for f in r.get('files') or [])]
            causes[m] = ((errs.get(m) or messages.get(m, '')[:1500] or 'error: failed in the global build')
                         + (' | the upstream sync changed this module or its imports (keep the upstream text; adapt our code)'
                            if upn else '')
                         + (' | changed in this build among the modules it imports (adapt this module to them): '
                            + ', '.join(ch[:10]) if ch else ''))
        try:
            rid, moved = red_rework.quarantine(set(orphan), causes, f"batch {b['id']} round {b['round'] + 1}")
        except red_rework.Refuse as x:
            # 2026-10-24: no mass move and no guessing: the failure stays for a worker (coord/build-errors has the
            # compiler message) and an alert is raised; the batch waits for the next build
            log(f"batch {b['id']}: ALERT rework move refused ({x}); the failure stays in the library for a worker")
            alert(b['id'], ' '.join(orphan[:6]), str(x)[:200], 'fix the failing module (coord/build-errors)')
            # 2026-10-25: the failing modules the batch's deliveries wrote still go back to their writers (below);
            # before, this branch returned first and they stayed in the library build after build
        else:
            log(f"batch {b['id']}: {len(orphan)} failing module(s) no delivery wrote -> rework, {len(moved)} module(s) "
                f"moved to quarantine/ (landing {rid or '-'}): {' '.join(orphan[:8])}")
    for d in decisions:
        log(f"batch {b['id']} red: {d['failure']} -> returned to its writer(s) {', '.join(d['return'])} (tools)")
    if decisions:
        execute(b, decisions, log, imports=imports)
    else:
        b['round'] += 1
        b['await_recovery'] = True
        write_json(OPEN, b)
    return 'returned'


def restore_after_fix(plan: dict, log) -> None:
    """2026-10-26 (the human, 22:40): a rework fix lands together with the quarantined importers it was blocking. A
    landing that writes a module of coord/rework.tsv (a quarantined root, now back at its original path: rework.landed)
    is followed, still under coord/.merge.lock, by the cluster restore (rework.cluster_restore, wait=False): every
    quarantined module no confirmed-unfixed root blocks comes back in the same snapshot, so the next global build
    verifies the fix and its whole downstream at once (before: fix -> build -> green -> restore -> another build;
    PQRU 1fc70eb18da landed while its 3641 importers stayed in quarantine/). A root whose quarantined text is the one
    that failed (local/rework-tried.json) still blocks (rework.cluster_set). What fails is taken out with its importers
    (batch_recovery.commit_inverse)."""
    try:
        import rework
        mods = {m.get("module") for m in (plan.get("D") or {}).get("modules") or []} | {plan.get("item")}
        fixed = sorted(m for m in mods & set(rework.load()) if m and rework.landed(m))
        if not fixed:
            return
        n = rework.cluster_restore(wait=False)
        chk = plan.get("rootfix") or {}
        log(f"rework fix landed ({' '.join(fixed[:4])}): {n} quarantined module(s) back in the same batch; the next "
            "build verifies them with the fix" + (" (root check: " + ", ".join(f"{m} {s}" for m, s in chk.items()) + ")" if chk else ""))
    except Exception as exc:  # noqa: BLE001
        log("rework restore after a fix failed (restore_when_idle tries again) |", repr(exc)[:300])


def build_running() -> bool:
    """a global build (tools/build.py) is running: local/builds/current.json names a live build.py pid and no `finished`"""
    cur = ld.read_json(ld.B / "current.json") or {}
    if cur.get("finished") or not cur.get("pid"):
        return False
    try:
        return b"build.py" in pathlib.Path(f"/proc/{int(cur['pid'])}/cmdline").read_bytes()
    except (OSError, ValueError):
        return False


def restore_when_idle(cache: dict, log) -> None:
    """2026-10-26 (the human, 22:25): the cluster restore does not wait for the next batch. Before, it ran only at the
    start of land_batch, so a module whose root fix had landed waited for a green build, the next batch and another
    build (IntegralOperationsScalarComparisons: fixed 21:59, back 22:19). Now, every lander step in which no global
    build runs, no retry round is open, the last build is green, no batch landing is mid-commit (local/batch/landing.json)
    and the repository changed since the last try (HEAD, or 10 min), rework.cluster_restore(wait=False) puts back what
    cluster_set() allows, under coord/.merge.lock and local/tree.lock (a build snapshot, also under the merge lock, takes
    all of it or none of it); the next build verifies it. land_batch keeps its own call.
    22:40 (the human): a fix committed into a quarantine/ copy while a build runs goes into the NEXT snapshot, so the
    restore no longer waits for the running build to end or for a green result; only a retry round (it rebuilds its
    own snapshot; what lands meanwhile is held back) and a batch landing mid-commit still wait."""
    if (BD / "landing.json").exists() or (BD / "proof-imports.json").exists() or _sync_running():
        return
    if retry_round_open():
        return
    head = md.git("rev-parse", "HEAD").strip()
    if cache.get("_idle_restore") == head and time.time() - cache.get("_idle_restore_t", 0) < 600:
        return
    cache["_idle_restore"], cache["_idle_restore_t"] = head, time.time()
    try:
        import rework
        n = rework.cluster_restore(wait=False)
        if n:
            log(f"rework restore between steps (no batch landing mid-commit): {n} quarantined module(s) back; the next build snapshot verifies them")
    except Exception as exc:  # noqa: BLE001
        log("rework restore while idle failed, tried again next step |", repr(exc)[:300])


def step(cache: dict, log) -> str:
    """One step of the cycle; returns what it did (idle, landed, waiting, verified, triage, returned)."""
    repairs.reconcile()
    try:
        import freeze
        freeze.update(log)       # 2026-10-28: the blocked freeze (more than 100 blocked: only rework fixes land)
    except Exception as exc:  # noqa: BLE001
        log("freeze update failed, the last state holds |", repr(exc)[:300])
    restore_when_idle(cache, log)
    # 2026-10-17 (xrhandoff): no dedicated repair service any more; open repair jobs go to the stage-3 queue at once
    # (coord/repairs.txt, see repair_queue.handoff), before counts() could re-take their XR claims.
    try:
        if any(v.startswith('released_to_queue') for _, _, v in repairs.handoff(log=log)):
            refresh_recovery_queue()
    except Exception as e:
        log('repair handoff failed, retried next step', repr(e)[:300])
    stats = repairs.counts()
    if cache.get('_repair_stats') != stats:
        log('REPAIR statistics', json.dumps(stats, sort_keys=True))
        cache['_repair_stats'] = stats
    try:
        cache.setdefault("_pre2", s2b.Prep()).pump(log)     # stage-2 checks run per delivery, also while a build runs
    except Exception as exc:  # noqa: BLE001
        log("stage 2: check pump failed |", repr(exc)[:300])
    b = read_json(OPEN)
    if not b and NEXT.exists():
        os.replace(NEXT, OPEN); b = read_json(OPEN)     # a stop between closing a batch and promoting the next one
    if _sync_running():
        if (ld.read_json(ld.B / "last.json") or {}).get("result") == "red":
            log("RED build during the upstream sync: left to the sync's quarantine (local/UPSYNC_RUNNING)")
            return "waiting"
    # 2026-10-25: in a retry round, a red build that contains none of the open batch's landings (the batch landed while
    # the build ran) is handled as one with no batch open; before rounds it waited for the next snapshot
    _lr = ld.read_json(ld.B / "last.json") or {}
    _foreign = (bool(b) and _lr.get("result") == "red" and retry_round_open()
                and not ({e["landing"] for e in b["entries"] if e["state"] == "landed"} & set(_lr.get("included") or [])))
    if (not b or _foreign) and ld.merge_queue() and red_without_batch(log):
        return "returned"
    # 2026-10-25: a red build whose handling is complete (the batch recorded it as handled, or the merge queue handled
    # it with no batch open) lets its clean landings land (land_rest; once per build)
    _last = ld.read_json(ld.B / "last.json") or {}
    if _last.get("result") == "red" and ((b and seen_red(b, _last) and not b.get("triage"))
                                        or (not b and _last.get("time") in (read_json(BD / "mq-red.json") or []))):
        try:
            land_rest(log)
        except Exception as exc:  # noqa: BLE001
            log("land_rest failed |", repr(exc)[:300])
        if b and _last.get("time") in (read_json(PARTIAL) or []) and isinstance(_last.get("clean"), list):
            # what of the batch neither failed nor compiled (it imports a failure no delivery of the batch wrote) stays
            # an open landing of the merge queue: a later build verifies it or drops it (drop_other_writers); the
            # batch closes and the next one lands now instead of waiting for that failure's repair
            sync_states(b, log)
            left = [e for e in b["entries"] if e["state"] == "landed"]
            if left:
                for e in left:
                    e["state"] = "queued"
                b.pop("await_recovery", None)
                write_json(OPEN, b)
                log(f"batch {b['id']}: {len(left)} landing(s) blocked by a failure they did not write stay in the merge "
                    "queue; the batch closes")
    if not b and retry_round_open():
        return "waiting"            # the next batch lands when the retry round is green (retry_round_open)
    if not b:
        return "landed" if land_batch(cache, log) else "idle"
    sync_states(b, log)
    nx = read_json(NEXT)
    if nx:
        sync_states(nx, log); write_json(NEXT, nx)
        if b.get('await_recovery') or b.get('triage'):
            b = fold_next(b, log); nx = None             # never two batches in recovery
    pend = [e for e in b["entries"] if e["state"] == "landed"]
    if b.get('await_recovery') and pend:     # 2026-10-25: nothing of the batch left open: it closes now (land_rest)
        last = ld.read_json(ld.B / 'last.json') or {}
        removed = {e['landing'] for e in b['entries'] if e['state'] in ('returned', 'waiting', 'reverted')}
        fresh = not seen_red(b, last) and not removed & set(last.get('included') or [])
        if not fresh: return 'waiting'
        if last.get('result') == 'green': b.pop('await_recovery', None)
        elif not pend: return 'waiting'
    if not pend:
        n = sum(e["state"] == "verified" for e in b["entries"])
        b["closed"] = ld.now()
        b["cycle_seconds"] = round(time.time() - calendar.timegm(time.strptime(b["time"], "%Y-%m-%dT%H:%M:%SZ")))
        write_json(CLOSED / f"{b['id']}.json", b)
        if NEXT.exists():
            os.replace(NEXT, OPEN)                       # the pipelined batch is the open one now
        else:
            OPEN.unlink(missing_ok=True)
        log(f"batch {b['id']} closed: {n} verified by the global build, {len(b['entries']) - n} not "
            f"({', '.join(key(e) + ' ' + e['state'] for e in b['entries'] if e['state'] != 'verified') or '-'}); "
            f"cycle {b['cycle_seconds']} s, {b['round']} round(s) of triage"
            + (f"; folded in: {', '.join(b['folded'])}" if b.get("folded") else "")
            + (f"; the pipelined batch {nx['id']} is the open one now" if nx else ""))
        clear_alert()
        return "verified"
    write_json(OPEN, b)
    if "_pre" in cache:
        cands = candidates(cache)
        cache["_pre"].pump(cands)
        pending_merge_jobs(cache["_pre"], cands, log)
    if b.get("triage"):
        t = b["triage"]
        v = read_json(pathlib.Path(t["dir"]) / "verdict.json")
        if v is None and time.time() < t["deadline"]:
            return "triage"
        if v is None:
            log(f"batch {b['id']}: no verdict from the triage agent in time; every suspect of an undecided failure is returned")
        ds = t["decisions"] + verdict_decisions(t["T"], v)
        for d in ds:
            log(f"batch {b['id']} triage: {d['failure']} -> {d['case']} ({d.get('by', 'tools')}), return {', '.join(d['return']) or 'nothing'}")
        pre = cache.get('_pre')
        imports = pre.snapshot() if hasattr(pre, 'snapshot') else library_imports()
        execute(b, ds, log, imports=imports)
        return "returned"
    # a red build is this batch's to handle when it contains landings of the batch that are still in the library and
    # none that was taken out since (a snapshot from before the last round), and was not handled already
    last = ld.read_json(ld.B / "last.json")
    inc = set((last or {}).get("included") or [])
    if not last or last.get("result") != "red" or seen_red(b, last):
        return maybe_pipeline(b, cache, log) or "waiting"
    ours = {e["landing"] for e in pend} | {e["landing"] for e in (nx or {}).get("entries", []) if e["state"] == "landed"}
    if not ours & inc or {e["landing"] for e in b["entries"] if e["state"] in ("returned", "reverted", "waiting")} & inc:
        return maybe_pipeline(b, cache, log) or "waiting"
    if nx:
        b = fold_next(b, log); nx = None
    pre = cache.get('_pre')
    imports = pre.snapshot() if hasattr(pre, 'snapshot') else library_imports()
    T = triage(b, last, imports)
    # Source attribution can outlive a build or a manual take-out. Discard its
    # decision before writing records/ALERT or taking anything out.
    if read_json(OPEN) != b or ld.read_json(ld.B / "last.json") != last:
        return "waiting"
    if _sync_running():
        log(f"batch {b['id']}: RED build during the upstream sync: left to the sync's quarantine (local/UPSYNC_RUNNING)")
        return "waiting"
    log(f"batch {b['id']}: RED build (round {b['round'] + 1}); failing {' '.join((last.get('failing') or [])[:8])}")
    # 2026-10-21 (the human): a landing of another writer whose OWN module fails (a restore from quarantine, a
    # maintainer landing) goes out at once, with the importers of its removed files; it was handed to the triage agent
    # as one of "several possible causes" and never taken out (the batch's execute() only returns batch deliveries), so
    # the same module failed build after build (ConstructibleExtContinuityStratum, SheafExtCoherent, 20:11-20:34).
    if ld.merge_queue() and drop_other_writers(b, last, list(last.get('failing') or []), log, persist=False, own_only=True):
        return "returned"
    b["handled"].append(last.get("time"))
    if last.get("source_fingerprint"):
        b.setdefault("handled_sources", []).append(last["source_fingerprint"])
    if os.environ.get("SHEAF_RED_MECHANICAL", "1") == "1":
        r = mechanical_red(b, last, log, imports)
        if r:
            land_rest(log)          # the failures are out: the rest of this build lands from it
            return r
    if T['unattributed'] and ld.merge_queue() and drop_other_writers(b, last, T['unattributed'], log):
        return 'returned'
    if T['unattributed'] or b['round'] >= 4:
        closure_fallback(b, last, log, imports)
        return 'returned'
    if T['open']:
        d = write_request(b, T)
        b["triage"] = {"dir": str(d), "deadline": time.time() + TRIAGE_WAIT, "decisions": T["decisions"], "T": {"open": T["open"]}}
        write_json(OPEN, b)
        log(f"batch {b['id']}: {len(T['open'])} failure(s) with several possible causes handed to the triage agent ({d.relative_to(ROOT)})")
        return "triage"
    for d in T["decisions"]:
        log(f"batch {b['id']} triage: {d['failure']} -> {d['case']} (tools), return {', '.join(d['return'])}")
    execute(b, T["decisions"], log, imports=imports)
    return "returned"


def _check_slot():
    """One of SHEAF_CHECK_SLOTS (default 16) machine-wide slots for a check-one process, held until it exits
    (2026-10-27: a lander restart left the old Pre pool's checks running beside the new pool's, 25+ checks at
    4.6 GB each plus their prune workers ran the host out of memory; POOL alone is per Pre instance)."""
    import fcntl
    n = max(1, int(os.environ.get("SHEAF_CHECK_SLOTS", "16")))
    d = ROOT / "local" / "check-slots"; d.mkdir(parents=True, exist_ok=True)
    while True:
        for i in range(n):
            f = open(d / f"{i}.lock", "w")
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return f
            except OSError:
                f.close()
        time.sleep(1)


def main(a: list[str]) -> int:
    def out(*x):
        print(time.strftime("%F %T"), *x, flush=True)
    if len(a) == 2 and a[0] == "check-one":      # run_checks
        c = json.load(sys.stdin); slot = _check_slot()   # noqa: F841   held until exit
        pathlib.Path(a[1]).write_bytes(pickle.dumps(_check(c))); return 0
    if a == ["step"]:
        print(step({}, out)); return 0
    if a == ["status"]:
        b = read_json(OPEN)
        if b:
            print(f"open batch {b['id']} (round {b['round']}{', waiting for the triage agent' if b.get('triage') else ''}):")
            for e in b["entries"]:
                print(f"  {e['state']:9} {key(e)} {e['head'][:9]} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
        else:
            print("no open batch")
        nx = read_json(NEXT)
        if nx:
            print(f"pipelined batch {nx['id']} (verified by the build after the open batch's):")
            for e in nx["entries"]:
                print(f"  {e['state']:9} {key(e)} {e['head'][:9]} landing {e['landing']} ({e['kind']}, {e['reviewer']})")
        for p in sorted(PASSED.glob("*.json")) if PASSED.is_dir() else []:
            m = read_json(p) or {}
            print(f"  passed, waiting for a batch: {m.get('group')}/{m.get('item')} {str(m.get('head'))[:9]} by {m.get('reviewer')}")
        return 0
    if len(a) >= 4 and a[0] in ("unland", "take-out"):
        path, b, e = OPEN, None, None
        for path in (OPEN, NEXT):
            b = read_json(path) or {"entries": []}
            e = next((e for e in b["entries"] if e["group"] == a[1] and e["item"] == a[2] and e["state"] == "landed"), None)
            if e: break
        if not e:
            print(f"{a[1]}/{a[2]} is not a landed delivery of the open (or pipelined) batch"); return 1
        if path == NEXT:      # a take-out may carry along landings of either batch: one open batch first
            b = fold_next(read_json(OPEN) or {}, out) if read_json(OPEN) else b
            path = OPEN if read_json(OPEN) else NEXT
            e = next(x for x in b["entries"] if x["landing"] == e["landing"])
        reason = " ".join(a[3:])
        try:
            unland(e, f"(the batch landing, head {e['head'][:9]}) taken out of the library again by the maintainer: {reason}", reason)
        except recovery.Conflict as exc:
            withdraw(b, 'take-out conflict: ' + str(exc), out)
            return 0
        e["state"] = "returned"; e["why"] = reason; write_json(path, b)
        return 0
    if a and a[0] == "pass":
        import argparse
        ap = argparse.ArgumentParser(prog="batch_land.py pass")
        ap.add_argument("group"); ap.add_argument("item"); ap.add_argument("--head"); ap.add_argument("--reviewer", default="reviewer")
        ap.add_argument("--spot-checked"); ap.add_argument("--verdict"); ap.add_argument("--apply-fixes"); ap.add_argument("--dry-run", action="store_true")
        try:
            return cmd_pass(ap.parse_args(a[1:]))
        except md.Fail as e:
            print(f"NOT MERGED {a[2] if len(a) > 2 else '?'}: {e}"); return 1
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
