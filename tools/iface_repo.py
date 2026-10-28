#!/usr/bin/env python3
"""The interface repository (the owner, 2026-10-28 17:20 CST): every delivery that changes a statement, a definition, an
instance, a notation or any other public interface goes here instead of into main.

Who decides: the REVIEW AGENT. A delivery is routed here when its judgement (tools/setbuild.py: the cc reviewer's
`interface` field of its verdict, or the judgement session; local/sets/results/<head>.json) says the statements or the
interface change (statement_unchanged false or downstream_affected true), or when its set build shows an interface
change (phase interface-changed), or when it deletes a module. The mechanical comparison (leanindex.interface_changes)
is reference only and routes nothing.

The repository. ~/weil-iface/repo is a git clone of the live repository (objects hardlinked), branch `iface`, started at
the FROZEN main (local/builds/published.json "commit", the last green global build). It does not follow main.
  - Its build tree is repo/lean/.lake: packages are a link to the live packages (never rebuilt: the build does not start
    when Lake would rebuild Mathlib), build/ is seeded by hardlinks from the published build (~/cc1/hlseed.py; Lake
    replaces compiled files by new inodes, .trace/.hash are made private), so a build compiles only what changed.
  - A routed delivery is APPLIED: its own changes (the branch against its merge base with main; for a replay, one
    landing commit) are put onto the iface branch with a three-way merge (`git apply -3`), a reviewer's FIX files on
    top, and committed. A conflict is left in the tree for the agent.
  - The maintainer agent (~/cc1/iface-agent: loop.py, BRIEF.md, a claude -p cycle on the review pool's tokens, like the
    PR agent) resolves conflicts and adapts every importer the change breaks, until the full build of the repository
    (the targets of the last green global build) is green.
  - Green = `lake build` succeeds on a clean, committed tree, no declaration that was sorry-free at the base has a
    `sorry` now, and no changed module uses an axiom beyond propext, Classical.choice, Quot.sound. A green build marks
    green every applied item it contains, and tags the commit iface-green/<stamp>.

When a statement-changing delivery is DONE (decision): when its change is green in the interface repository, i.e. the
first green build that contains it, with every downstream module of the repository compiling. Then (mode `on`) its
item is marked done on the task list (tools/queue_mark.py done 3). It reaches main at the merge; its claim and its
delivery branch are closed then.

Merge back into main (rule 3). The repository merges back only when
  (a) it is completely fixed: the last build is green at the tip, nothing is queued, in conflict or applied but not
      green; or
  (b) it is older than SHEAF_IFACE_MAX_AGE (1 day) since its first applied item: then the LAST GREEN commit is merged
      (the items applied after it stay and are applied again after the reset). Nothing green yet: no merge, an alert.
  merge-prepare: in the repository, branch `merge` = live sheaf-dag (main, M) merged with the chosen iface commit
      (`git merge --no-ff`, like a GitHub PR merge); conflicts are left for the agent, who resolves and commits.
  merge-build: the MERGE GLOBAL BUILD: the full build of the candidate (main + the interface changes, every target),
      with the same green rules, in the repository's build tree at the global build's priority (weilbuild.slice).
  merge-land (mode `on` only): only if main has not moved (sheaf-dag == M, no uncommitted Lean change), under
      coord/.merge.lock and local/tree.lock: live sheaf-dag fast-forwards to the candidate, the change is recorded as
      one landing of the writer `I` (kind interface), the candidate's compiled files are copied into the global build's
      copy (local/buildtree/.lake/build), and tools/build.py --only <that landing and the landings already waiting>
      runs ONCE: it compiles nothing the candidate build compiled, checks, publishes, advances sheaf-verified.
      Green: the candidate is the new frozen main; the items are closed (claim done, branch deleted, ledger line), and
      the repository is reset from the new main. Red: the landing is reverted at once (tools/landing.py revert), main
      is as before, the agent works on.
  Main is never broken by an interface change: nothing lands in main before the full candidate built green.

Set builds and the merge build. Set builds (tools/setbuild.py) always compile against the frozen tree (the published
build); they go on during the whole merge build, which runs in this repository's tree, not in the published one. Only
the publish at the end changes the frozen tree (local/PUBLISHING while it copies; setbuild waits for it and builds a set
again when the published build changed under it). A passed set whose modules import a module the merge changed is
listed by merge-prepare; setbuild builds it again on the new frozen tree.

Resource priority (cgroup slices; ~/cc1/bg-sweeper.py): set builds weilset.slice (CPUWeight 2000) > the merge global
build and the global build weilbuild.slice (1000) > ordinary work (100) >= interface-repository builds weiliface.slice
(100, nice 10) > background weilbg.slice (20). Each build moves itself into its slice before Lake starts. Every build
stops (Lake keeps what it compiled) while MemAvailable is below SHEAF_IFACE_MEM_STOP_GB (45) and resumes above
SHEAF_IFACE_MEM_RESUME_GB (80).

Pause (rule 4; mode `on`): while a change is pending here, the queue (tools/queue.py) does not offer
  - the modules the repository changes or a queued delivery will change (they belong to the interface work), and
  - the stage-2 nodes and stage-3 modules whose node depends directly (stmt_deps, proof_deps, proof-step uses) on a node
    whose statement the repository changes.
They come back by themselves after the merge. Work in the repository by workers: not offered (the simplest correct
option); the agent adapts what the change breaks.

Proof-only work in main is never blocked: main lands and builds as before; only the routed deliveries leave it.

Switch: local/iface/MODE (`off`, `shadow`, `on`; the environment SHEAF_IFACE overrides). shadow: routing is recorded and
the whole repository side runs (apply, agent, builds, merge candidate and its build), but nothing in main, the queue or
the lander changes and merge-land refuses. on: the lander leaves routed deliveries alone (tools/batch_land.py), the queue
pauses, green marks done, merge-land runs.

Usage (live repository, tools/iface_repo.py):
  status                         mode, repository, items, last builds, merge state
  tick                           one deterministic step of the loop (intake, apply, build, merge); prints JSON with
                                 `agent`: the reasons the agent must work now (conflict, red, merge conflict)
  intake                         route the deliveries the review agent judged statement-changing
  intake --add <G> <item> [--head <sha>] [--why <text>]    route one delivery branch by hand
  intake --replay <commit>...    (tests, shadow) route past landing commits ("Prove <item> (<G>, ...)") as deliveries
  init [--base <commit>] [--force]   (re)create the repository at the frozen main (or <commit>)
  apply [<G> <item>]             apply the queued deliveries (or one)
  reapply <G> <item>             (the agent) apply a delivery in conflict again, leaving the conflict markers in the tree
  applied <G> <item>             the agent resolved an apply conflict and committed: record it applied
  build [--merge]                full build of the repository (or of the merge candidate, at merge priority)
  errors [<module>]              the failing modules of the last build, or one module's compiler output
  compile <file.lean>            one file against the repository's build (lean -j1, LEAN_NUM_THREADS=1)
  return <G> <item> <reason>     the change cannot be made to work: revert it here, return it to its writer (mode on)
  merge-prepare [<commit>]       make the merge candidate (branch `merge`); conflicts are left for the agent
  merge-resolved                 the agent committed the resolution of the candidate's conflicts
  merge-build | merge-land       the merge global build of the candidate; landing it in main (mode on)
  paused                         the seeds of the pause (JSON), as tools/queue.py reads them
"""
from __future__ import annotations
import fcntl, json, os, pathlib, re, shutil, signal, subprocess, sys, time

TOOLS = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS))
ROOT = TOOLS.parent
if not (ROOT / "dag").exists():
    ROOT = pathlib.Path.home() / "weil-conjectures-sheaf"
H = pathlib.Path.home()
HOME = pathlib.Path(os.environ.get("SHEAF_IFACE_HOME") or (H / "weil-iface"))
REPO = HOME / "repo"
RLEAN = REPO / "lean"
ST = ROOT / "local" / "iface"
ITEMS = ST / "items"
BUILDS = ST / "builds"
ERRS = HOME / "build-errors"
LOGF = ST / "iface.log"
PUB = ROOT / "local" / "builds" / "published.json"
MAIN = "sheaf-dag"
BRANCH = "iface"
OK_AXIOMS = ("propext", "Classical.choice", "Quot.sound")
SKIP_PATHS = ("coord/claims/", "coord/ledger.md", "coord/deliveries.log", "coord/returns/", "coord/queue", "local/",
              "tools/", "roles/", "stages/", ".gitignore")
ACTIVE = ("queued", "conflict", "applied", "green")
AUTHOR = ("Bin Wu", "844524296@qq.com")


def env_setting(name: str, default: str) -> str:
    v = os.environ.get(name)
    if v:
        return v
    try:
        for line in (ROOT / "coord" / "sheaf.env").read_text().splitlines():
            if line.startswith(name + "="):
                return line.split("=", 1)[1].strip().strip('"')
    except OSError:
        pass
    return default


def mode() -> str:
    m = os.environ.get("SHEAF_IFACE")
    if not m:
        try:
            m = (ST / "MODE").read_text().strip()
        except OSError:
            m = "off"
    return m if m in ("off", "shadow", "on") else "off"


def now() -> str:
    return time.strftime("%FT%TZ", time.gmtime())


def log(*a) -> None:
    ST.mkdir(parents=True, exist_ok=True)
    with open(LOGF, "a") as f:
        f.write(time.strftime("%F %T ") + " ".join(str(x) for x in a) + "\n")


def read_json(p):
    try:
        return json.loads(pathlib.Path(p).read_text())
    except (OSError, ValueError):
        return None


def write_json(p, d) -> None:
    p = pathlib.Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + f".tmp{os.getpid()}")
    tmp.write_text(json.dumps(d, indent=1, ensure_ascii=False))
    os.replace(tmp, p)


def run(cmd, cwd=None, timeout=None, env=None, input=None) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env, input=input)


def git(repo, *a, check=False, input=None) -> str:
    r = run(["git", "-C", str(repo), *a], input=input)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(a[:3])}: {(r.stderr or r.stdout).strip()[:500]}")
    return r.stdout


def rgit(*a, **k) -> str:
    return git(REPO, *a, **k)


def lgit(*a, **k) -> str:
    return git(ROOT, *a, **k)


def commit_env() -> dict:
    return dict(os.environ, GIT_AUTHOR_NAME=AUTHOR[0], GIT_AUTHOR_EMAIL=AUTHOR[1], GIT_COMMITTER_NAME=AUTHOR[0],
                GIT_COMMITTER_EMAIL=AUTHOR[1])


def published() -> dict:
    return read_json(PUB) or {}


def targets() -> list[str]:
    """The targets of the last green global build (its source_fingerprint `|targets:a,b`), else the lakefile's default."""
    fp = published().get("source_fingerprint") or ""
    m = re.search(r"\|targets:([\w.,]+)", fp)
    return [t for t in m.group(1).split(",") if t] if m else []


def state() -> dict:
    return read_json(ST / "state.json") or {}


def save_state(s: dict) -> None:
    write_json(ST / "state.json", s)


def key(g: str, item: str) -> str:
    return f"{g}__{item}"


def item_path(g: str, item: str) -> pathlib.Path:
    return ITEMS / f"{key(g, item)}.json"


def items(states=None) -> list[dict]:
    out = []
    for p in sorted(ITEMS.glob("*.json")) if ITEMS.is_dir() else []:
        r = read_json(p)
        if r and (states is None or r.get("state") in states):
            out.append(r)
    return sorted(out, key=lambda r: (r.get("routed") or "", r["group"], r["item"]))


def save_item(r: dict, event: str | None = None) -> None:
    if event:
        r.setdefault("history", []).append(f"{now()} {event}")
        r["history"] = r["history"][-30:]
    write_json(item_path(r["group"], r["item"]), r)


def mem_available_gb() -> float:
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1048576
    except OSError:
        pass
    return 1e9


def disk_used_pct(path: pathlib.Path) -> float:
    st = os.statvfs(path)
    return 100.0 * (1 - st.f_bavail / st.f_blocks) if st.f_blocks else 0.0


def module_of(rel: str) -> str:
    """lean/A/B.lean -> A.B"""
    return rel[len("lean/"):-len(".lean")].replace("/", ".") if rel.startswith("lean/") else rel[:-len(".lean")].replace("/", ".")


# ---------------------------------------------------------------- routing (rule 1: the review agent decides)

def judged_statement_changing(r: dict) -> str | None:
    """The reason a set-build result routes its delivery here, None when it does not."""
    if not isinstance(r, dict):
        return None
    ph, j = r.get("phase"), r.get("judgement") or {}
    if ph == "interface-changed":
        return "set build: " + str(r.get("why") or "a changed module's interface changed")[:300]
    if ph == "not-eligible":
        if isinstance(j.get("statement_unchanged"), bool) and isinstance(j.get("downstream_affected"), bool) \
                and (not j["statement_unchanged"] or j["downstream_affected"]):
            what = "statements/interface change" if not j["statement_unchanged"] else "downstream affected"
            return f"review agent ({j.get('source') or '?'}): {what}: " + str(j.get("reasoning") or "")[:300]
        if "deletes a module" in str(r.get("why") or ""):
            return "the delivery deletes a module"
    return None


def claim_who(item: str):
    return (read_json(ROOT / "coord" / "claims" / f"{item}.lock") or {}).get("who")


def branch_head(g: str, item: str) -> str:
    return lgit("rev-parse", "-q", "--verify", f"refs/heads/deliver/{g}/{item}").strip()


def delivery_paths(base: str, head: str, repo=None) -> list[str]:
    repo = repo or ROOT
    out = []
    for p in git(repo, "diff", "--name-only", "--no-renames", base, head).split("\n"):
        if p and not p.startswith(SKIP_PATHS) and "/.sandbox/" not in p and "/.lake/" not in p:
            out.append(p)
    return out


def node_changes(base: str, head: str, paths: list[str], repo=None) -> list[str]:
    """Node ids whose statement or Lean record the change rewrites (existing nodes) or adds."""
    repo = repo or ROOT
    out = []
    for p in paths:
        if not (p.startswith("dag/nodes/") and p.endswith(".json")):
            continue
        try:
            new = json.loads(git(repo, "show", f"{head}:{p}") or "null")
        except ValueError:
            continue
        if not isinstance(new, dict):
            continue
        try:
            old = json.loads(git(repo, "show", f"{base}:{p}") or "null") or {}
        except ValueError:
            old = {}
        if old.get("statement") != new.get("statement") or (old.get("lean") or {}).get("decl") != (new.get("lean") or {}).get("decl") \
                or old.get("stmt_deps") != new.get("stmt_deps"):
            out.append(str(new.get("id") or pathlib.Path(p).stem))
    return sorted(set(out))


def new_item(g, item, head, src, why, base=None, extra=None) -> dict:
    r = {"group": g, "item": item, "head": head, "src": src, "from": base, "state": "queued", "why": why,
         "routed": now(), "mode_at_routing": mode()}
    r.update(extra or {})
    b = base or lgit("merge-base", MAIN, head).strip()
    paths = delivery_paths(b, head)
    r["paths"] = paths
    r["modules"] = sorted(module_of(p) for p in paths if p.startswith("lean/") and p.endswith(".lean"))
    r["nodes"] = node_changes(b, head, paths)
    return r


def intake(add=None, replay=(), why_text=None) -> list[dict]:
    """Route deliveries. Returns the new or updated item records."""
    ITEMS.mkdir(parents=True, exist_ok=True)
    out = []
    if add:
        g, item, head = add
        head = head or branch_head(g, item)
        if not head:
            raise SystemExit(f"no branch deliver/{g}/{item}")
        out.append(_route(g, item, head, "branch", why_text or "routed by hand"))
        return [x for x in out if x]
    for c in replay:
        c = lgit("rev-parse", c).strip()
        msg = lgit("show", "-s", "--format=%s", c).strip()
        m = re.match(r"Prove (\S+) \((\w+),", msg)
        if not m:
            print(f"{c[:10]}: not a landing commit ('Prove <item> (<G>, ...)'): {msg[:80]}")
            continue
        item, g = m.group(1), m.group(2)
        out.append(_route(g, item, c, "commit", why_text or f"replay of landing {c[:10]} ({msg[:100]})", base=c + "^"))
    if add or replay:
        return [x for x in out if x]
    res_dir = ROOT / "local" / "sets" / "results"
    for p in sorted(res_dir.glob("*.json")) if res_dir.is_dir() else []:
        r = read_json(p) or {}
        why = judged_statement_changing(r)
        if not why:
            continue
        g, item, head = r.get("group"), r.get("item"), r.get("head")
        if not (g and item and head) or branch_head(g, item) != head or claim_who(item) != g:
            continue
        out.append(_route(g, item, head, "branch", why))
    return [x for x in out if x]


def _route(g, item, head, src, why, base=None):
    cur = read_json(item_path(g, item))
    if cur and cur.get("head") == head:
        return None
    if cur and cur.get("state") in ("applied", "green", "conflict"):
        # a new head of an item already applied: the difference to the applied head is applied next (rule: the newest
        # head of the writer wins; the agent keeps the importers' adaptations)
        cur.update(head=head, state="queued", why=why, src=src, prev_applied=cur.get("applied_head"))
        save_item(cur, f"new head {head[:12]} routed; applied {str(cur.get('applied_head'))[:12]} stays, the difference is applied")
        log("intake", g, item, head[:9], "new head of an applied item")
        return cur
    r = new_item(g, item, head, src, why, base=base)
    save_item(r, f"routed ({why[:160]})")
    log("intake", g, item, head[:9], src, why[:200])
    return r


def routed_head(g: str, item: str, head: str) -> bool:
    """tools/batch_land.py: this head goes to the interface repository, not into main (mode on only)."""
    if mode() != "on":
        return False
    r = read_json(item_path(g, item))
    return bool(r) and r.get("state") in ACTIVE + ("merging",) and r.get("head") == head


# ---------------------------------------------------------------- the repository

def ensure_lake() -> None:
    lake = RLEAN / ".lake"
    lake.mkdir(parents=True, exist_ok=True)
    pk = lake / "packages"
    live_pk = os.path.realpath(ROOT / "lean" / ".lake" / "packages")
    if not pk.is_symlink():
        if pk.exists():
            raise SystemExit(f"{pk} exists and is not a link to the live packages")
        pk.symlink_to(live_pk)
    if not (lake / "build").exists():
        src = os.path.realpath(ROOT / "lean" / ".lake" / "build")
        r = run([sys.executable, "-I", str(H / "cc1" / "hlseed.py"), src, str(lake / "build")])
        if r.returncode != 0:
            raise SystemExit("hlseed failed: " + (r.stderr or r.stdout)[-500:])
        log("build tree seeded by hardlinks from", src)
    # the published copy leaves out ir/ (tools/build.py publish), but every module's trace names its .c output there:
    # without it Lake rebuilds everything (measured 2026-10-28: 3375 modules out of date). Taken from the global build's
    # copy (hardlinks; a module whose .c there belongs to a newer build is rebuilt, nothing else)
    ir, bir = lake / "build" / "ir", ROOT / "local" / "buildtree" / ".lake" / "build" / "ir"
    if not ir.exists() and bir.is_dir():
        r = run(["cp", "-al", str(bir), str(ir)])
        if r.returncode == 0:
            run([sys.executable, "-I", str(H / "cc1" / "hlseed.py"), "--fix", str(ir)])
            log("ir/ seeded by hardlinks from", bir)
        else:
            log("ir/ not seeded:", r.stderr[-300:])


def init(base: str | None = None, force: bool = False) -> dict:
    """(Re)create the repository at the frozen main. Keeps the clone and its build tree (a reset is a checkout)."""
    if disk_used_pct(H) > 85:
        raise SystemExit(f"disk {disk_used_pct(H):.0f}% used: no new tree")
    base = base or published().get("commit")
    if not base:
        raise SystemExit("no published commit")
    busy = [r for r in items(("applied", "green", "conflict")) if not force]
    if busy and (REPO / ".git").exists():
        raise SystemExit(f"{len(busy)} item(s) applied and not merged; use --force to drop them (they are queued again)")
    HOME.mkdir(parents=True, exist_ok=True)
    if not (REPO / ".git").exists():
        r = run(["git", "clone", "-q", "--no-checkout", str(ROOT), str(REPO)])
        if r.returncode != 0:
            raise SystemExit("clone failed: " + r.stderr[-500:])
        rgit("config", "user.name", AUTHOR[0]); rgit("config", "user.email", AUTHOR[1])
        rgit("config", "gc.auto", "0")
        rgit("remote", "rename", "origin", "live")
    rgit("fetch", "-q", "live", f"+refs/heads/{MAIN}:refs/remotes/live/{MAIN}")
    if not rgit("cat-file", "-t", base).strip():
        rgit("fetch", "-q", "live", base)
    rgit("merge", "--abort")
    rgit("cherry-pick", "--abort")
    rgit("reset", "-q", "--hard")
    r = run(["git", "-C", str(REPO), "checkout", "-q", "-f", "-B", BRANCH, base])
    if r.returncode != 0:
        raise SystemExit("checkout failed: " + r.stderr[-500:])
    rgit("clean", "-q", "-fd", "-e", ".lake")
    ensure_lake()
    for r in items(("applied", "green", "conflict", "merging")):
        r.update(state="queued", applied_head=None, applied_commit=None, prev_applied=None)
        save_item(r, f"repository reset to {base[:12]}: queued again")
    s = {"base": base, "base_time": published().get("time"), "created": now(), "first_applied": None,
         "last_build": None, "last_green": None, "merge": None}
    save_state(s)
    log("init at", base[:12])
    return s


def dirty() -> list[str]:
    return [l for l in rgit("status", "--porcelain", "--untracked-files=normal", "--", "lean", "dag", "coord").split("\n")
            if l and "/.lake/" not in l and "/.sandbox/" not in l]


FIX_DIR = ROOT / "local" / "verdicts" / "3"


def fix_files(g: str, item: str, head: str, paths: list[str]) -> dict:
    """A reviewer's FIX files (local/verdicts/3/<head>/fixes/<base name>) mapped onto the delivery's paths, as the lander
    applies them: <Module>.lean, <node-id>.json, <name>.change.md, <item>.report.md."""
    v = read_json(FIX_DIR / f"{head}.json") or {}
    fx = FIX_DIR / head / "fixes"
    if v.get("verdict") != "FIX" or not fx.is_dir():
        return {}
    by_name = {}
    for p in paths:
        by_name.setdefault(pathlib.PurePosixPath(p).name, p)
    out = {}
    for f in sorted(fx.iterdir()):
        if not f.is_file():
            continue
        n = f.name
        if n.endswith(".report.md"):
            out[f"coord/reports/{g}/{n[:-len('.report.md')]}.md"] = f.read_text()
        elif n.endswith(".change.md"):
            out[f"coord/changes/{n[:-len('.change.md')]}.md"] = f.read_text()
        elif n in by_name:
            out[by_name[n]] = f.read_text()
    return out


def apply_one(r: dict, keep: bool = False) -> str:
    """Apply one queued delivery onto the iface branch. Returns 'applied', 'conflict', 'empty' or 'gone'. A conflict is
    recorded and the tree put back (so the other deliveries apply meanwhile); with `keep` (the agent's `reapply`) the
    conflict markers stay in the tree for the agent to resolve."""
    g, item, head = r["group"], r["item"], r["head"]
    if r.get("src") == "branch":
        if branch_head(g, item) != head:
            r["state"] = "superseded"; save_item(r, "branch moved or gone before apply"); return "gone"
        rgit("fetch", "-q", "live", f"+refs/heads/deliver/{g}/{item}:refs/iface/deliver/{g}/{item}")
    else:
        rgit("fetch", "-q", "live", f"+refs/heads/{MAIN}:refs/remotes/live/{MAIN}")
    if not rgit("cat-file", "-t", head).strip():
        r["state"] = "superseded"; save_item(r, "head not fetchable"); return "gone"
    if dirty():
        raise RuntimeError("the repository has uncommitted changes; the agent finishes them first")
    frm = r.get("prev_applied") or r.get("from") or lgit("merge-base", MAIN, head).strip()
    frm = rgit("rev-parse", frm).strip() or frm
    paths = delivery_paths(frm, head, REPO)
    if not paths:
        r.update(state="applied", applied_head=head, applied_commit=rgit("rev-parse", "HEAD").strip(), prev_applied=None)
        save_item(r, "nothing to apply (no change against the applied head)"); return "empty"
    patch = run(["git", "-C", str(REPO), "diff", "--binary", "--no-renames", frm, head, "--", *paths]).stdout
    a = run(["git", "-C", str(REPO), "apply", "-3", "--index", "--whitespace=nowarn"], input=patch)
    over = fix_files(g, item, head, paths)
    for p, text in over.items():
        f = REPO / p
        f.parent.mkdir(parents=True, exist_ok=True)
        f.write_text(text)
        rgit("add", "--", p)
    for p in paths:   # a change record of the delivery: status as the lander writes it
        if p.startswith("coord/changes/") and (REPO / p).is_file():
            t = (REPO / p).read_text()
            t2 = re.sub(r"(?m)^(## Status\n+)open\b.*$", f"\\1applied in the interface repository {now()[:10]} "
                        f"(deliver/{g}/{item} {head[:12]})", t)
            if t2 != t:
                (REPO / p).write_text(t2); rgit("add", "--", p)
    unmerged = [l[3:] for l in rgit("status", "--porcelain").split("\n") if l[:2] in ("UU", "AA", "DU", "UD", "AU", "UA")]
    if a.returncode != 0 or unmerged:
        r.update(state="conflict", conflict_files=unmerged or paths[:20], conflict_from=frm,
                 apply_error=(a.stderr or "")[-1500:])
        save_item(r, f"apply conflict in {len(unmerged)} file(s): {' '.join(unmerged[:6])}")
        log("apply", g, item, head[:9], "CONFLICT", " ".join(unmerged[:6]))
        if not keep:
            rgit("reset", "-q", "--hard", "HEAD")
        return "conflict"
    msg = (f"Apply {item} ({g}, deliver {head[:12]}) in the interface repository\n\n{r.get('why', '')[:600]}\n"
           + (f"Reviewer FIX files: {', '.join(sorted(over))}\n" if over else "")
           + f"Changed from {frm[:12]}: {len(paths)} file(s).\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n")
    c = run(["git", "-C", str(REPO), "commit", "-q", "-m", msg], env=commit_env())
    if c.returncode != 0 and "nothing to commit" not in (c.stdout + c.stderr):
        raise RuntimeError("commit failed: " + (c.stderr or c.stdout)[-400:])
    mark_applied(r)
    return "applied"


def mark_applied(r: dict) -> None:
    r.update(state="applied", applied_head=r["head"], applied_commit=rgit("rev-parse", "HEAD").strip(), prev_applied=None,
             conflict_files=None, apply_error=None, applied=now())
    save_item(r, f"applied at {r['applied_commit'][:12]}")
    s = state()
    if not s.get("first_applied"):
        s["first_applied"] = now(); save_state(s)
    log("apply", r["group"], r["item"], r["head"][:9], "applied", r["applied_commit"][:9])


def apply_all(only=None) -> dict:
    res = {}
    if dirty():
        return {"waiting": "uncommitted changes in the repository (the agent's work)"}
    st = state().get("merge") or {}
    if st.get("phase") not in (None, "done", "aborted"):
        return {"waiting": f"merge in progress ({st.get('phase')}); new deliveries wait for the reset"}
    for r in items(("queued",)):
        if only and (r["group"], r["item"]) != only:
            continue
        res[key(r["group"], r["item"])] = apply_one(r)
    return res


# ---------------------------------------------------------------- builds

SLICES = {"iface": "weiliface.slice", "merge": "weilbuild.slice"}


def in_slice(kind: str, cmd: list[str]) -> list[str]:
    """The command, started after its shell moved itself into the build's cgroup slice (children inherit it)."""
    procs = f"/sys/fs/cgroup/{SLICES[kind]}/cgroup.procs"
    if not os.path.exists(procs):
        return cmd
    return ["sh", "-c", f'echo $$ | sudo -n tee {procs} >/dev/null 2>&1; exec "$@"', "sh", *cmd]


def packages_ok() -> bool:
    r = run(["lake", "build", "--no-build", "Mathlib"], cwd=RLEAN, env=lake_env())
    if r.returncode != 0:
        log("packages check failed: Lake would rebuild Mathlib in the shared packages; not built", (r.stdout + r.stderr)[-300:])
        return False
    return True


def lake_env(threads: str = "1") -> dict:
    return dict(os.environ, PATH=f"{H}/.elan/bin:" + os.environ.get("PATH", ""), LEAN_NUM_THREADS=threads)


def parse_failing(text: str) -> list[str]:
    return sorted(set(re.findall(r"^✖ \[\d+/\d+\] \S+ (\S+)", text, re.M)))


def save_errors(text: str) -> dict:
    """{module: compiler output} of every failing job (as tools/build.py save_errors), also written to build-errors/."""
    blocks, cur = {}, None
    for line in text.split("\n"):
        m = re.match(r"^[✖✔⚠] \[\d+/\d+\] \S+ (\S+)", line)
        if m:
            cur = m.group(1) if line.startswith("✖") else None
            if cur:
                blocks.setdefault(cur, [])
            continue
        if cur is not None and not line.startswith("trace:"):
            blocks[cur].append(line)
    if ERRS.is_dir():
        for p in ERRS.glob("*.txt"):
            p.unlink()
    ERRS.mkdir(parents=True, exist_ok=True)
    for m, lines in blocks.items():
        (ERRS / f"{m}.txt").write_text("\n".join(lines)[:40000])
    return {m: "\n".join(l)[:4000] for m, l in blocks.items()}


def lake_build(kind: str, logp: pathlib.Path) -> tuple[int, float, str]:
    """`lake build <targets>` in the repository, in the build's slice; stops while memory is short (Lake keeps the
    compiled modules) and starts again. Returns (rc, seconds, output)."""
    stop_gb = float(env_setting("SHEAF_IFACE_MEM_STOP_GB", "45"))
    resume_gb = float(env_setting("SHEAF_IFACE_MEM_RESUME_GB", "80"))
    nice = "0" if kind == "merge" else "10"
    threads = env_setting("SHEAF_BUILD_THREADS", "3") if kind == "merge" else "2"
    cmd = in_slice(kind, ["nice", "-n", nice, "lake", "build", *targets()])
    t0 = time.time()
    attempts = 0
    while True:
        while mem_available_gb() < (resume_gb if attempts else stop_gb):
            time.sleep(30)
        attempts += 1
        with open(logp, "w") as lf:
            p = subprocess.Popen(cmd, cwd=RLEAN, stdout=lf, stderr=subprocess.STDOUT, env=lake_env(threads),
                                 start_new_session=True)
            stopped = False
            while p.poll() is None:
                time.sleep(15)
                if mem_available_gb() < stop_gb:
                    os.killpg(p.pid, signal.SIGTERM)
                    try:
                        p.wait(timeout=60)
                    except subprocess.TimeoutExpired:
                        os.killpg(p.pid, signal.SIGKILL); p.wait()
                    stopped = True
                    log(f"{kind} build stopped: MemAvailable {mem_available_gb():.0f} GB < {stop_gb:.0f} GB; resumes above {resume_gb:.0f}")
                    break
        if stopped and attempts < 20:
            continue
        return p.returncode, round(time.time() - t0, 1), logp.read_text(errors="ignore")


def sorry_regressions(base: str, head: str, repo=None) -> tuple[list[str], list[str]]:
    """(declarations sorry-free at `base` that have a `sorry` at `head`, declarations of `base` removed at `head`) in the
    Lean files changed between them. Text check (tools/stage3_delivery.decl_table)."""
    import stage3_delivery as s3
    repo = repo or REPO
    regress, removed = [], []
    for p in git(repo, "diff", "--name-only", "--no-renames", base, head, "--", "lean").split("\n"):
        if not p.endswith(".lean"):
            continue
        old = git(repo, "show", f"{base}:{p}")
        if not old:
            continue
        new = git(repo, "show", f"{head}:{p}")
        try:
            to, tn = s3.decl_table(old), s3.decl_table(new or "")
        except Exception as e:  # noqa: BLE001
            regress.append(f"{p}: declarations not readable ({e!r})"[:200]); continue
        for k, d in to.items():
            if k not in tn:
                if not new or not d.get("private"):
                    removed.append(f"{module_of(p)}: {d.get('name') or k}"[:200])
                continue
            if not d.get("sorry") and tn[k].get("sorry"):
                regress.append(f"{module_of(p)}: {d.get('name') or k} had no sorry at {base[:10]} and has one now"[:300])
    return regress, removed


def probe_axioms(mods: list[str], kind: str = "iface") -> tuple[list[str], str]:
    """Axioms beyond propext, Classical.choice, Quot.sound used by declarations of `mods` (tools/build.py BATCH_PROBE),
    run with `lake env lean` in the repository after a successful build."""
    if not mods:
        return [], ""
    from build import BATCH_PROBE  # noqa: E402
    d = RLEAN / ".sandbox"
    d.mkdir(exist_ok=True)
    f = d / "IfaceProbe.lean"
    found, tail = [], ""
    for i in range(0, len(mods), 200):
        part = mods[i:i + 200]
        f.write_text("import Lean.Elab.Command\n" + "".join(f"import {m}\n" for m in part)
                     + BATCH_PROBE % ",\n    ".join("`" + m for m in part))
        r = run(in_slice(kind, ["nice", "-n", "0" if kind == "merge" else "10", "timeout", "900", "lake", "env", "lean", str(f)]), cwd=RLEAN,
                env=lake_env("1"))
        out = r.stdout + r.stderr
        tail = out[-2000:]
        for m in part:
            if not re.search(r"SHEAF-PROBED " + re.escape(m) + r" \d+", out):
                found.append(f"{m}: the probe did not run ({tail[-300:]})")
        for m, c, a in re.findall(r"SHEAF-AXIOM (\S+) (\S+) (\S+)", out):
            if a not in OK_AXIOMS and a != "sorryAx":
                found.append(f"{m}: {c} uses the axiom {a}")
    f.unlink(missing_ok=True)
    return found, tail


def build(kind: str = "iface") -> dict:
    """Full build of the repository's working tree. kind iface: the iface branch; merge: the merge candidate."""
    HOME.mkdir(parents=True, exist_ok=True)
    lockf = open(HOME / "build.lock", "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        return {"result": "busy", "why": "another build of the repository runs"}
    s = state()
    head = rgit("rev-parse", "HEAD").strip()
    dt = dirty()
    stamp = time.strftime("%Y%m%dT%H%M%S")
    BUILDS.mkdir(parents=True, exist_ok=True)
    logp = HOME / "logs" / f"{kind}-{stamp}.log"
    logp.parent.mkdir(parents=True, exist_ok=True)
    rec = {"time": now(), "kind": kind, "commit": head, "dirty": dt[:20], "base": s.get("base"), "log": str(logp),
           "targets": targets()}
    if not packages_ok():
        rec.update(result="infra", why="Lake would rebuild Mathlib in the shared packages")
    else:
        log(f"{kind} build of {head[:12]}" + (f" (+{len(dt)} uncommitted)" if dt else "") + " started")
        rc, secs, text = lake_build(kind, logp)
        failing = parse_failing(text)
        rec.update(seconds=secs, rc=rc, failing=failing)
        if rc != 0:
            save_errors(text)
            rec.update(result="red", why=(f"{len(failing)} failing module(s)" if failing else text[-1500:]))
        else:
            base = (s.get("merge") or {}).get("main") if kind == "merge" else s.get("base")
            changed = [module_of(p) for p in rgit("diff", "--name-only", "--no-renames", base, "--", "lean").split("\n")
                       if p.endswith(".lean") and (RLEAN / p[len("lean/"):]).is_file()] if base else []
            regress, removed = sorry_regressions(base, head) if base and not dt else ([], [])
            ax, _tail = probe_axioms(changed, kind)
            rec.update(changed=len(changed), sorry_regressions=regress, removed_declarations=removed[:200], axioms=ax)
            if regress or ax:
                rec.update(result="red", why="; ".join((regress + ax)[:6])[:1500])
            else:
                rec.update(result="green")
    write_json(BUILDS / f"{stamp}-{kind}.json", rec)
    s = state()
    s["last_merge_build" if kind == "merge" else "last_build"] = rec
    if rec["result"] == "green" and not dt:
        if kind == "iface":
            s["last_green"] = {"commit": head, "time": rec["time"]}
            rgit("tag", "-f", f"iface-green/{stamp}", head)
        else:
            s["merge"] = dict(s.get("merge") or {}, phase="built", built=head, build=rec["time"])
    elif kind == "merge" and rec["result"] == "red":
        s["merge"] = dict(s.get("merge") or {}, phase="red", build=rec["time"])
    save_state(s)
    log(f"{kind} build of {head[:12]}: {rec['result'].upper()} " + str(rec.get("why") or "")[:300])
    if rec["result"] == "green" and not dt and kind == "iface":
        mark_green(head)
    return rec


def is_ancestor(a: str, b: str) -> bool:
    return run(["git", "-C", str(REPO), "merge-base", "--is-ancestor", a, b]).returncode == 0


def mark_green(head: str) -> None:
    done = []
    for r in items(("applied",)):
        if r.get("applied_commit") and is_ancestor(r["applied_commit"], head):
            r.update(state="green", green_commit=head, green=now())
            save_item(r, f"green at {head[:12]}: done")
            done.append(r["item"])
    if done and mode() == "on":
        run([sys.executable, str(TOOLS / "queue_mark.py"), "done", "3", *done, "--note",
             f"green in the interface repository at {head[:12]} (tools/iface_repo.py)"], cwd=ROOT, timeout=300)
    if done:
        log("green:", " ".join(done))


# ---------------------------------------------------------------- merge back into main

def merge_due() -> tuple[str | None, str]:
    """(commit to merge, why) or (None, why not)."""
    s = state()
    applied = items(("applied", "green"))
    if not applied:
        return None, "nothing applied"
    lb, lg = s.get("last_build") or {}, s.get("last_green") or {}
    tip = rgit("rev-parse", BRANCH).strip()
    open_ = items(("queued", "conflict", "applied"))
    if lg.get("commit") == tip and not open_ and not dirty():
        return tip, "completely fixed: green at the tip, nothing queued, in conflict or waiting"
    age_h = float(env_setting("SHEAF_IFACE_MAX_AGE_H", "24"))
    first = s.get("first_applied")
    if first:
        import calendar
        age = (time.time() - calendar.timegm(time.strptime(first, "%Y-%m-%dT%H:%M:%SZ"))) / 3600
        if age > age_h:
            if lg.get("commit") and any(r["state"] == "green" for r in applied):
                return lg["commit"], f"older than {age_h:g} h ({age:.1f} h): the last green commit is merged"
            return None, f"older than {age_h:g} h ({age:.1f} h) but nothing green yet"
    return None, f"not fixed yet (last build {lb.get('result')}, {len(open_)} item(s) open)"


def merge_prepare(commit: str | None = None) -> dict:
    s = state()
    if commit is None:
        commit, why = merge_due()
        if not commit:
            return {"phase": "not-due", "why": why}
    else:
        why = "by hand"
    if dirty():
        return {"phase": "waiting", "why": "uncommitted changes in the repository"}
    rgit("fetch", "-q", "live", f"+refs/heads/{MAIN}:refs/remotes/live/{MAIN}")
    main = rgit("rev-parse", f"refs/remotes/live/{MAIN}").strip()
    merged_items = [r for r in items(("green", "applied")) if r.get("applied_commit") and is_ancestor(r["applied_commit"], commit)
                    and r["state"] == "green"]
    rgit("tag", "-f", "iface-merge-source", commit)
    co = run(["git", "-C", str(REPO), "checkout", "-q", "-f", "-B", "merge", main])
    if co.returncode != 0:
        return {"phase": "error", "why": co.stderr[-400:]}
    names = ", ".join(r["item"] for r in merged_items[:30])
    msg = (f"Merge the interface repository into main ({len(merged_items)} statement-changing deliveries)\n\n{why}.\n"
           f"Items: {names}\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n")
    m = run(["git", "-C", str(REPO), "merge", "--no-ff", "-q", "-m", msg, commit], env=commit_env())
    unmerged = [l[3:] for l in rgit("status", "--porcelain").split("\n") if l[:2] in ("UU", "AA", "DU", "UD", "AU", "UA")]
    st = {"phase": "conflict" if (m.returncode != 0 or unmerged) else "prepared", "main": main, "source": commit,
          "why": why, "items": [key(r["group"], r["item"]) for r in merged_items], "time": now(),
          "conflicts": unmerged[:200]}
    for r in merged_items:
        r["state"] = "merging"; save_item(r, f"in the merge candidate (main {main[:12]})")
    st["affected_passed_sets"] = affected_passed_sets(commit)
    s["merge"] = st
    save_state(s)
    log("merge-prepare", st["phase"], "main", main[:12], "source", commit[:12], len(merged_items), "item(s)",
        ("conflicts: " + " ".join(unmerged[:8])) if unmerged else "")
    return st


def affected_passed_sets(commit: str) -> list[str]:
    """Passed sets (tools/setbuild.py) whose modules import a module the interface change touches: built again by
    setbuild on the new frozen tree after the merge publishes."""
    base = state().get("base")
    if not base:
        return []
    changed = {module_of(p) for p in rgit("diff", "--name-only", base, commit, "--", "lean").split("\n") if p.endswith(".lean")}
    out = []
    pdir = ROOT / "local" / "sets" / "passed"
    for p in sorted(pdir.glob("*.json")) if pdir.is_dir() else []:
        r = read_json(p) or {}
        folder = pathlib.Path(r.get("folder") or "")
        hit = False
        for m in r.get("modules") or []:
            f = folder / "src" / (m.replace(".", "/") + ".lean")
            try:
                import import_cycles as ic
                if set(ic.imports(f.read_text())) & changed:
                    hit = True; break
            except Exception:  # noqa: BLE001
                continue
        if hit:
            out.append(f"{r.get('group')}/{r.get('item')} {str(r.get('head'))[:12]}")
    return out


def merge_build() -> dict:
    s = state()
    st = s.get("merge") or {}
    if st.get("phase") not in ("prepared", "red", "resolved"):
        return {"result": "skip", "why": f"merge phase {st.get('phase')}"}
    if rgit("rev-parse", "--abbrev-ref", "HEAD").strip() != "merge":
        return {"result": "skip", "why": "the repository is not on the merge branch"}
    if dirty() or [l for l in rgit("status", "--porcelain").split("\n") if l[:2] in ("UU", "AA")]:
        return {"result": "skip", "why": "unresolved or uncommitted merge"}
    return build("merge")


def merge_land() -> dict:
    """The candidate becomes main (mode on only); see the module text."""
    if mode() != "on":
        return {"result": "refused", "why": f"mode {mode()}: merge-land only in mode on"}
    s = state()
    st = s.get("merge") or {}
    cand = rgit("rev-parse", "merge").strip()
    if st.get("phase") != "built" or st.get("built") != cand:
        return {"result": "refused", "why": "the candidate has no green merge build at its tip"}
    import landing as ld  # noqa: E402
    import mergelock  # noqa: E402
    if (ROOT / "local" / "batch" / "landing.json").exists():
        return {"result": "wait", "why": "a batch landing is being committed"}
    main = st["main"]
    lgit("fetch", "-q", str(REPO), f"+refs/heads/merge:refs/iface/candidate")
    with open(mergelock.LOCK, "a") as lockf:
        try:
            mergelock.acquire(lockf, mergelock.LOCK, 600)
        except mergelock.LockTimeout as e:
            return {"result": "wait", "why": str(e)}
        try:
            with ld.tree_lock():
                if lgit("rev-parse", MAIN).strip() != main or lgit("symbolic-ref", "--short", "HEAD").strip() != MAIN:
                    st["phase"] = "stale"; s["merge"] = st; save_state(s)
                    return {"result": "stale", "why": "main moved since the candidate was made: merge-prepare again"}
                if lgit("status", "--porcelain", "--", "lean").strip():
                    return {"result": "wait", "why": "uncommitted Lean changes in main"}
                changed = [p for p in lgit("diff", "--name-only", "--no-renames", main, cand, "--", "lean").split("\n")
                           if p.endswith(".lean")]
                before = {}
                for p in changed:
                    b = run(["git", "-C", str(ROOT), "show", f"{main}:{p}"]).stdout
                    before[p[len("lean/"):]] = b.encode() if lgit("cat-file", "-t", f"{main}:{p}").strip() else None
                ff = run(["git", "-C", str(ROOT), "merge", "-q", "--ff-only", cand])
                if ff.returncode != 0:
                    return {"result": "error", "why": "fast-forward failed: " + (ff.stderr or ff.stdout)[-500:]}
                rec = ld.new_record("I", before, f"merge of the interface repository ({len(st.get('items') or [])} "
                                    f"statement-changing deliveries; candidate {cand[:12]})", kind="interface",
                                    extra={"iface": {"candidate": cand, "main": main, "items": st.get("items")}})
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)
    waiting = [r["id"] for r in ld.records(ld.REQUESTS)]
    (ST / "merge-landings.txt").write_text("\n".join(waiting) + "\n")
    st.update(phase="landed", landing=rec["id"], landed=now(), candidate=cand); s["merge"] = st; save_state(s)
    log("merge-land: main fast-forwarded to", cand[:12], "landing", rec["id"])
    return merge_verify()


def merge_verify() -> dict:
    """After merge-land: the candidate's compiled files into the global build's copy, then ONE global build
    (tools/build.py --only) of exactly what main holds; green closes the items and resets the repository, red reverts."""
    import landing as ld  # noqa: E402
    s = state()
    st = s.get("merge") or {}
    if st.get("phase") != "landed":
        return {"result": "skip", "why": f"merge phase {st.get('phase')}"}
    cand, rid = st["candidate"], st["landing"]
    ids = ST / "merge-landings.txt"
    # the candidate's compiled files into the global build's copy, then ONE global build of exactly what main holds
    bl = open(ld.B / "build.lock", "w")
    for _ in range(240):
        try:
            fcntl.flock(bl, fcntl.LOCK_EX | fcntl.LOCK_NB); break
        except OSError:
            time.sleep(15)
    else:
        return {"result": "wait", "why": "the global build lock stayed busy; landed, build pending"}
    try:
        r = run(["rsync", "-a", f"{RLEAN}/.lake/build/", f"{ROOT}/local/buildtree/.lake/build/"])
    finally:
        fcntl.flock(bl, fcntl.LOCK_UN); bl.close()
    if r.returncode != 0:
        log("merge-verify: copy of the compiled files failed (the build compiles them itself):", r.stderr[-300:])
    b = run([sys.executable, str(TOOLS / "build.py"), "--only", str(ids)], cwd=ROOT,
            env=dict(os.environ, SHEAF_LEAD="L-only", PATH=f"{H}/.elan/bin:" + os.environ.get("PATH", "")))
    if b.returncode == 2 and "Another global build is running" in b.stdout:
        return {"result": "wait", "why": "another global build is running; landed, build pending"}
    last = read_json(ld.B / "last.json") or {}
    green = b.returncode == 0 and last.get("result") == "green" and rid in (last.get("verified") or [])
    if not green:
        rv = revert_merge(st)
        st.update(phase="red", reverted=now(), revert=rv[-300:]); s["merge"] = st; save_state(s)
        log("merge-verify: global build NOT green; merge reverted in main:", rv[-200:])
        return {"result": "red", "why": str(last.get("failing") or b.stdout[-500:])[:800]}
    close_merged(st, cand)
    s = state(); st.update(phase="done", published=published().get("commit")); s["merge"] = st; save_state(s)
    init(published().get("commit"), force=True)
    return {"result": "green", "published": published().get("commit")}


def revert_merge(st: dict) -> str:
    """Main as before the merge: the landing reverted (tools/landing.py revert: the Lean files, the record closed), every
    other file of the merge put back to main's version, one commit; under coord/.merge.lock."""
    import mergelock  # noqa: E402
    main, cand, rid = st["main"], st["candidate"], st["landing"]
    out = ""
    with open(mergelock.LOCK, "a") as lockf:
        mergelock.acquire(lockf, mergelock.LOCK, 1800)
        try:
            rv = run([sys.executable, str(TOOLS / "landing.py"), "revert", rid,
                      "merge global build of the interface repository not green"], cwd=ROOT, env=dict(os.environ, SHEAF_LEAD="L-only"))
            out += rv.stdout + rv.stderr
            paths = [p for p in lgit("diff", "--name-only", "--no-renames", main, cand).split("\n") if p]
            for p in paths:
                if p.endswith(".lean") and p.startswith("lean/"):
                    continue
                if lgit("cat-file", "-t", f"{main}:{p}").strip():
                    lgit("checkout", main, "--", p)
                else:
                    lgit("rm", "-q", "-f", "--", p)
            lgit("add", "-A", "--", *paths)
            c = run(["git", "-C", str(ROOT), "commit", "-q", "-m",
                     f"Revert the merge of the interface repository (candidate {cand[:12]}): global build not green\n\n"
                     "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n", "--", *paths], env=dict(commit_env(), SHEAF_LEAD="L-only"))
            out += c.stdout + c.stderr
        finally:
            fcntl.flock(lockf, fcntl.LOCK_UN)
    for k in st.get("items") or []:
        r = read_json(ITEMS / f"{k}.json")
        if r and r.get("state") == "merging":
            r["state"] = "green"; save_item(r, "merge reverted in main (global build red): back to green")
    return out


def close_merged(st: dict, cand: str) -> None:
    """Close the merged items in main as the lander closes a landing: claim done, branch deleted, ledger line."""
    import merge_delivery as md  # noqa: E402
    paths = ["coord/ledger.md"]
    for k in st.get("items") or []:
        r = read_json(ITEMS / f"{k}.json")
        if not r:
            continue
        g, item = r["group"], r["item"]
        if claim_who(item) == g:
            run([sys.executable, str(TOOLS / "claim.py"), "done", g, item, f"merged with the interface repository ({cand[:12]})"],
                cwd=ROOT, env=dict(os.environ, SHEAF_LEAD="L-only"))
            paths.append(f"coord/claims/{item}.lock")
        if r.get("src") == "branch" and branch_head(g, item) == r.get("head"):
            lgit("update-ref", "-d", f"refs/heads/deliver/{g}/{item}", r["head"])
        md.ledger_line(f"merged deliver/{g}/{item} through the interface repository (candidate {cand[:12]}; "
                       f"green at {str(r.get('green_commit'))[:12]})")
        r["state"] = "merged"; save_item(r, f"merged into main ({cand[:12]})")
    paths = [p for p in paths if lgit("status", "--porcelain", "--", p).strip()]
    if paths:
        with open(ROOT / "coord" / ".merge.lock", "a") as lf:
            fcntl.flock(lf, fcntl.LOCK_EX)
            run(["git", "-C", str(ROOT), "add", "-A", "--", *paths])
            run(["git", "-C", str(ROOT), "commit", "-q", "-m", "Close the deliveries merged with the interface repository\n\n"
                 "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>\n", "--", *paths],
                env=dict(commit_env(), SHEAF_LEAD="L-only"))
    queue_done = [read_json(ITEMS / f"{k}.json")["item"] for k in st.get("items") or [] if (ITEMS / f"{k}.json").exists()]
    if queue_done:
        run([sys.executable, str(TOOLS / "queue_mark.py"), "done", "3", *queue_done, "--note", "merged with the interface repository"],
            cwd=ROOT, timeout=300)


def return_item(g: str, item: str, reason: str) -> dict:
    """The change cannot be made to work: revert its apply commit here and (mode on) return it to its writer."""
    r = read_json(item_path(g, item))
    if not r:
        return {"result": "no such item"}
    if r.get("applied_commit") and r["state"] in ("applied", "green"):
        rv = run(["git", "-C", str(REPO), "revert", "--no-edit", r["applied_commit"]], env=commit_env())
        if rv.returncode != 0:
            return {"result": "revert failed", "why": (rv.stderr or rv.stdout)[-500:]}
    elif r["state"] == "conflict":
        rgit("reset", "-q", "--hard")
    r["state"] = "returned"; save_item(r, f"returned: {reason[:300]}")
    if mode() == "on" and r.get("src") == "branch":
        run([sys.executable, str(TOOLS / "merge_delivery.py"), "return", g, item,
             f"interface repository: {reason}"], cwd=ROOT, env=dict(os.environ, SHEAF_LEAD="L-only"))
    log("return", g, item, reason[:200])
    return {"result": "returned"}


# ---------------------------------------------------------------- pause (rule 4)

def pause_seeds() -> dict:
    """{"modules": [...], "nodes": [...]} the pending interface work holds: modules changed in the repository against
    its base or by a queued delivery, and the nodes whose statement those changes rewrite."""
    mods, nodes = set(), set()
    s = state()
    base = s.get("base")
    for r in items(ACTIVE + ("merging",)):
        mods.update(r.get("modules") or []); nodes.update(r.get("nodes") or [])
    if base and (REPO / ".git").exists():
        tip = rgit("rev-parse", BRANCH).strip()
        paths = [p for p in rgit("diff", "--name-only", "--no-renames", base, tip).split("\n") if p]
        mods.update(module_of(p) for p in paths if p.startswith("lean/") and p.endswith(".lean"))
        try:
            nodes.update(node_changes(base, tip, paths, REPO))
        except Exception:  # noqa: BLE001
            pass
    return {"modules": sorted(mods), "nodes": sorted(nodes), "time": now()}


def paused_sets(g, seeds: dict | None = None) -> tuple[set, set, dict]:
    """(paused node ids, paused modules, why) for tools/queue.py: the seed modules, the seed nodes' DIRECT dependents
    (stmt_deps, proof_deps, uses) and their modules. Empty unless mode on."""
    if mode() != "on":
        return set(), set(), {}
    seeds = seeds if seeds is not None else (read_json(ST / "paused.json") or {})
    smods, snodes = set(seeds.get("modules") or []), set(seeds.get("nodes") or [])
    if not smods and not snodes:
        return set(), set(), {}
    import dag_queue  # noqa: E402
    why = {m: "changed in the interface repository" for m in smods}
    nodes = set()
    for j, d in g.live.items():
        deps = set(g.deps(j, "all"))
        hit = deps & snodes
        if hit:
            nodes.add(j); why.setdefault(j, f"depends on {sorted(hit)[0]}, whose statement changes in the interface repository")
    mods = set(smods)
    for j in nodes:
        m = dag_queue.module_of(g.live[j])
        if m:
            mods.add(m); why.setdefault(m, why[j])
    return nodes, mods, why


# ---------------------------------------------------------------- the loop step

def tick() -> dict:
    out = {"mode": mode(), "time": now(), "agent": []}
    if mode() == "off":
        return out
    if not (REPO / ".git").exists() or not state().get("base"):
        out["init"] = init()["base"]
    out["intake"] = [key(r["group"], r["item"]) for r in intake()]
    s = state()
    st = s.get("merge") or {}
    ph = st.get("phase")
    if ph == "conflict":
        out["agent"].append(f"merge conflict in the candidate: {', '.join(st.get('conflicts') or [])[:400]}")
    elif ph in ("prepared", "resolved"):
        out["merge_build"] = b = merge_build()
        if b.get("result") == "red":
            out["agent"].append(f"the merge candidate is red: {b.get('why')}")
    elif ph == "red":
        lmb = s.get("last_merge_build") or {}
        if lmb.get("commit") != rgit("rev-parse", "HEAD").strip():
            out["merge_build"] = b = merge_build()
            if b.get("result") == "red":
                out["agent"].append(f"the merge candidate is red: {b.get('why')}")
        else:
            out["agent"].append(f"the merge candidate is red: {lmb.get('why')}")
    if (state().get("merge") or {}).get("phase") == "landed":
        out["merge_verify"] = merge_verify()
    if (state().get("merge") or {}).get("phase") == "built":
        if mode() == "on":
            out["merge_land"] = merge_land()
        else:
            out["merge_land"] = {"result": "shadow", "why": "the candidate is green; mode shadow: not landed"}
    ph = (state().get("merge") or {}).get("phase")
    if ph in (None, "done", "aborted", "stale"):
        if ph == "stale":
            rgit("checkout", "-q", "-f", BRANCH)
            s = state(); s["merge"] = None; save_state(s)
            for r in items(("merging",)):
                r["state"] = "green"; save_item(r, "merge candidate stale: back to green")
        if rgit("rev-parse", "--abbrev-ref", "HEAD").strip() != BRANCH and not dirty():
            rgit("checkout", "-q", BRANCH)
        out["apply"] = apply_all()
        conf = [r for r in items(("conflict",))]
        if conf:
            out["agent"].append("apply conflict: " + "; ".join(f"{r['group']}/{r['item']} ({', '.join((r.get('conflict_files') or [])[:5])})" for r in conf))
        else:
            lb = state().get("last_build") or {}
            tip = rgit("rev-parse", "HEAD").strip()
            if items(("applied",)) and (lb.get("commit") != tip or lb.get("dirty")) and not dirty():
                out["build"] = b = build("iface")
                if b.get("result") == "red":
                    out["agent"].append(f"the repository is red: {b.get('why')}")
            elif lb.get("result") == "red" and lb.get("commit") == tip:
                out["agent"].append(f"the repository is red: {lb.get('why')}")
            commit, why = merge_due()
            out["merge_due"] = why
            if commit and not out["agent"]:
                out["merge_prepare"] = mp = merge_prepare(commit)
                if mp.get("phase") == "conflict":
                    out["agent"].append("merge conflict in the candidate: " + ", ".join(mp.get("conflicts") or [])[:400])
                elif mp.get("phase") == "prepared":
                    out["merge_build"] = b = merge_build()
                    if b.get("result") == "red":
                        out["agent"].append(f"the merge candidate is red: {b.get('why')}")
    if dirty() and not out["agent"]:
        out["agent"].append("uncommitted changes in the repository (an unfinished agent cycle)")
    write_json(ST / "paused.json", pause_seeds())
    write_json(ST / "tick.json", out)
    return out


def status() -> int:
    s = state()
    print(f"mode {mode()}; repository {REPO} ({'present' if (REPO / '.git').exists() else 'absent'})")
    if s:
        print(f"base {str(s.get('base'))[:12]} (published {s.get('base_time')}); created {s.get('created')}; first applied {s.get('first_applied')}")
        for k in ("last_build", "last_merge_build"):
            b = s.get(k) or {}
            if b:
                print(f"{k}: {b.get('result')} at {str(b.get('commit'))[:12]} {b.get('time')} {b.get('seconds', '-')} s; "
                      f"failing {len(b.get('failing') or [])}; {str(b.get('why') or '')[:200]}")
        lg = s.get("last_green") or {}
        if lg:
            print(f"last green: {lg.get('commit', '')[:12]} {lg.get('time')}")
        m = s.get("merge") or {}
        if m:
            print(f"merge: {m.get('phase')} main {str(m.get('main'))[:12]} source {str(m.get('source'))[:12]} items {len(m.get('items') or [])}")
        print("merge due:", merge_due()[1] if (REPO / ".git").exists() else "-")
    by = {}
    for r in items():
        by.setdefault(r["state"], []).append(r)
    for stt, rs in sorted(by.items()):
        print(f"{stt}: {len(rs)}")
        for r in rs[:40]:
            print(f"  {r['group']}/{r['item']} {r['head'][:10]} {r.get('src')} modules {len(r.get('modules') or [])} "
                  f"nodes {len(r.get('nodes') or [])}  {str(r.get('why') or '')[:100]}")
    return 0


def compile_file(f: str) -> int:
    p = pathlib.Path(f).resolve()
    if RLEAN.resolve() not in p.parents:
        print(f"{p} is not under {RLEAN}"); return 2
    r = subprocess.run(in_slice("iface", ["nice", "-n", "10", "timeout", env_setting("SHEAF_FILE_RUN_LIMIT", "300"),
                                          "lake", "env", "lean", "-j1", str(p)]), cwd=RLEAN, env=lake_env("1"))
    return r.returncode


def main(a: list[str]) -> int:
    if not a or a[0] in ("-h", "--help"):
        print(__doc__); return 0
    c = a[0]
    if c == "status":
        return status()
    if c == "tick":
        print(json.dumps(tick(), indent=1, ensure_ascii=False)); return 0
    if c == "intake":
        why = a[a.index("--why") + 1] if "--why" in a else None
        if "--add" in a:
            i = a.index("--add")
            head = a[a.index("--head") + 1] if "--head" in a else None
            rs = intake(add=(a[i + 1], a[i + 2], head), why_text=why)
        elif "--replay" in a:
            rest = [x for x in a[a.index("--replay") + 1:] if not x.startswith("--")]
            if "--why" in a:
                rest = [x for x in rest if x != why]
            rs = intake(replay=rest, why_text=why)
        else:
            rs = intake()
        for r in rs:
            print(f"routed {r['group']}/{r['item']} {r['head'][:12]}: {len(r.get('modules') or [])} module(s), nodes {', '.join(r.get('nodes') or []) or '-'}")
        return 0
    if c == "init":
        base = a[a.index("--base") + 1] if "--base" in a else None
        print(json.dumps(init(base, force="--force" in a), indent=1)); return 0
    if c == "apply":
        print(json.dumps(apply_all((a[1], a[2]) if len(a) >= 3 else None), indent=1)); return 0
    if c == "reapply" and len(a) >= 3:
        r = read_json(item_path(a[1], a[2]))
        if not r or r.get("state") != "conflict":
            print("no conflict recorded for that item"); return 1
        if dirty():
            print("the tree has uncommitted changes: commit or reset them first"); return 1
        out = apply_one(r, keep=True)
        print(out + ("" if out != "conflict" else ": resolve the markers in " + " ".join(r.get("conflict_files") or [])
                     + ", commit, then run `applied " + a[1] + " " + a[2] + "`"))
        return 0
    if c == "applied" and len(a) >= 3:
        r = read_json(item_path(a[1], a[2]))
        if not r or r.get("state") != "conflict":
            print("no conflict recorded for that item"); return 1
        if dirty() or [l for l in rgit("status", "--porcelain").split("\n") if l[:2] in ("UU", "AA")]:
            print("commit the resolution first (the tree has uncommitted changes)"); return 1
        mark_applied(r); print("applied"); return 0
    if c == "build":
        r = build("merge" if "--merge" in a else "iface")
        print(json.dumps({k: v for k, v in r.items() if k != "removed_declarations"}, indent=1)[:4000])
        return 0 if r.get("result") == "green" else 1
    if c == "errors":
        if len(a) > 1:
            p = ERRS / f"{a[1]}.txt"
            print(p.read_text() if p.exists() else "no error recorded for that module"); return 0
        for p in sorted(ERRS.glob("*.txt")) if ERRS.is_dir() else []:
            print(p.stem)
        return 0
    if c == "compile" and len(a) == 2:
        return compile_file(a[1])
    if c == "return" and len(a) >= 4:
        print(json.dumps(return_item(a[1], a[2], " ".join(a[3:])))); return 0
    if c == "merge-prepare":
        print(json.dumps(merge_prepare(a[1] if len(a) > 1 else None), indent=1)); return 0
    if c == "merge-resolved":
        s = state(); st = s.get("merge") or {}
        if st.get("phase") != "conflict" or dirty() or [l for l in rgit("status", "--porcelain").split("\n") if l[:2] in ("UU", "AA")]:
            print("no merge conflict recorded, or the resolution is not committed"); return 1
        st["phase"] = "resolved"; s["merge"] = st; save_state(s); print("resolved"); return 0
    if c == "merge-build":
        r = merge_build(); print(json.dumps(r, indent=1)[:3000]); return 0 if r.get("result") == "green" else 1
    if c == "merge-land":
        r = merge_land(); print(json.dumps(r, indent=1)); return 0 if r.get("result") == "green" else 1
    if c == "paused":
        print(json.dumps(pause_seeds(), indent=1)); return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
