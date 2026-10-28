#!/usr/bin/env python3
"""Set builds: a delivery the review agent judges statement-preserving is DONE when its own modules compile on the
frozen tree (the owner, 2026-10-28: "现在的工作是否完成不看全局编译的结果，而看部分集合编译的结果"; final design 17:00 CST,
review of 18:20 applied).

The frozen tree is the published library: the sources of the last green global build (local/builds/published.json)
and its compiled files lean/.lake/build/lib/lean, in the version local/builds/publish-gen ("N done"; tools/build.py
writes "N publishing" before a publish and "N done" after published.json). A set build reads that version at its
start and refuses the result when it changed by its end. Nothing here ever writes into the frozen tree.

A' = every Lean module the delivery changes or adds, in a folder of its own that is never rebuilt once complete:
local/sets/<G>__<item>__<head12>__<texts sha8>__g<N>-<frozen commit8>/ with src/ (the set's sources), new/ (the
compiled NEW modules: no frozen version), changed/ (the compiled CHANGED modules X'), set.json, evaluation.json.
  - Gates first (as the lander's check): read_delivery's static checks, no `#exit`, sorry_ledger.missing_gate, no
    import cycle closed, every import in the FROZEN tree or the set (another set's new module: wait until it is
    merged and published).
  - The new modules compile first, in import order, each with the set's earlier new modules; then every changed module
    in parallel against the frozen tree ALONE (the other changed modules in their frozen, old version) plus the
    set's new modules. The set's compiled modules are handed to Lean by --setup importArts (Lean takes the FIRST
    LEAN_PATH root holding Sheaf/, so a second root cannot add modules). `lean -j1`, LEAN_NUM_THREADS=1; over 60 s is
    a failure.
  - Rule 4: a changed module that fails alone and compiles with the set's other changed modules in front (directly, or
    through up to 10 unchanged intermediates rebuilt against them; ~/cc1/between.py) shows an interface change:
    `interface-changed`, never a pass, logged (judgement-wrong.tsv, intermediates.tsv); more than 10 intermediates:
    `interface-path`.
  - Probe: a module-system file with `import all` of the set's modules (all from the set's own folder): no `sorry`
    the delivery may not leave, no axiom beyond propext, Classical.choice, Quot.sound, and every named declaration of
    the sources present in the compiled module.
  - Judgement (rule 1): the cc reviewer's `interface` field of its PASS/FIX verdict (local/verdicts/3/<head>.json), or
    a judgement session of our own (local/sets/judge/<head>__<sha12>.json, a claude -p on the review pool) that sees
    the diffs, the mechanical comparison of tools/leanindex.py and the compile (whether each changed module's public
    .olean is byte-identical to the frozen one) as reference only.
Pass = all of it. With the switch `on` the pass is recorded (local/sets/passed/<head>.json: id, folder, modules, new
modules, head, frozen version, judgement), the item is marked done (tools/queue_mark.py done --source-dir <set src>),
tools/pending_deps.py counts it as a pass (dependents released), tools/own_decl.py reads its modules from the set
(progress, queue), and its new modules are visible to worker compiles (local/sets/_new, tools/remote_compile_set.py).
A pass holds only while the head is the branch head, the verdict is not RETURN, the latest evaluation is a pass of
the same texts and the judgement is still eligible; the daemon revokes it otherwise (queue_mark rework), and so does
tools/batch_land.py when the delivery lands with other texts. Two unmerged passed sets never change the same module.
Merging A' into the library and the frozen .olean happens later: the ordinary batch landing and the next global build.

Measured 2026-10-28 (Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare, proof changed): the public .olean is
byte-identical after a proof-only change (module system; .olean.server/.olean.private/.ilean differ) and Lake then
takes its importers as up to date even in hash mode.

Switch: the file local/sets/MODE: `off`, `shadow` (judge and set-build the waiting deliveries, record results, change
nothing else) or `on`. (SHEAF_SETBUILD_TEST_MODE overrides it, for tests only.)

Usage:
  tools/setbuild.py daemon               the loop (~/cc1/setbuild-loop.sh; pid local/sets/daemon.pid)
  tools/setbuild.py status               mode, frozen version, results by phase
  tools/setbuild.py report [--hours H]   results against what the ordinary path later did with the same heads
  tools/setbuild.py build <G> <module> [--no-judge]   evaluate one delivery branch now
  tools/setbuild.py validate <head>      shadow check of a pass: direct importers, frozen vs with the set
Settings (environment or coord/sheaf.env): SHEAF_SETBUILD_SETS (3 set builds at once, machine-wide),
SHEAF_SETBUILD_PAR (4 compiles of one set at once), SHEAF_SETBUILD_JUDGES (4), SHEAF_SETBUILD_JUDGE_TIMEOUT (900 s),
SHEAF_SETBUILD_MIN_MEM_GB (60), SHEAF_FILE_RUN_LIMIT (120 s: how long Lean may run for its messages; 60 s passes).
"""
from __future__ import annotations
import os as _os, sys as _sys
# tools/queue.py shadows the standard `queue` that concurrent.futures needs (as in tools/build.py): import it first
# without tools/ on the path
_saved = list(_sys.path)
_here = _os.path.dirname(_os.path.abspath(__file__))
_sys.path[:] = [p for p in _sys.path if _os.path.abspath(p or ".") != _here]
_sys.modules.pop("queue", None)
import queue as _queue  # noqa: E402,F401
import concurrent.futures as cf  # noqa: E402
_sys.path[:] = _saved
import fcntl, hashlib, json, os, pathlib, re, shutil, subprocess, sys, threading, time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import leanindex as li  # noqa: E402

ROOT = li.ROOT
LEAN = li.LEAN
SB = ROOT / "local" / "sets"
RESULTS, JUDGE, PASSED, NEWLINK = SB / "results", SB / "judge", SB / "passed", SB / "_new"
LOG = SB / "setbuild.log"
PUB = ROOT / "local" / "builds" / "published.json"
PUBLIB = LEAN / ".lake" / "build" / "lib" / "lean"
CFG = li.config()
PROJECT = ("Sheaf.", "WeilConjectures.")
SVC = pathlib.Path.home() / "weil-review-svc"
LEANBIN = str(pathlib.Path.home() / ".elan" / "bin" / "lean")
OK_AXIOMS = ("propext", "Classical.choice", "Quot.sound")


def setting(name: str, default: str) -> str:
    return os.environ.get(name) or CFG.get(name) or default


def mode() -> str:
    m = os.environ.get("SHEAF_SETBUILD_TEST_MODE")      # tests only; the switch is the file local/sets/MODE
    if not m:
        try:
            m = (SB / "MODE").read_text().strip()
        except OSError:
            m = "off"
    return m if m in ("off", "shadow", "on") else "off"


def log(*a) -> None:
    SB.mkdir(parents=True, exist_ok=True)
    with open(LOG, "a") as f:
        f.write(time.strftime("%F %T ") + " ".join(str(x) for x in a) + "\n")


def read_json(p):
    try:
        return json.loads(pathlib.Path(p).read_text())
    except (OSError, ValueError):
        return None


def write_json(p, d) -> None:
    p = pathlib.Path(p)
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + f".tmp{os.getpid()}.{threading.get_ident()}")
    tmp.write_text(json.dumps(d, indent=1, ensure_ascii=False))
    os.replace(tmp, p)


def git(*a) -> str:
    r = subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else ""


def published() -> dict:
    return read_json(PUB) or {}


def published_commit() -> str:
    return published().get("commit") or ""


def module_of(rel: str) -> str:
    return rel[:-len(".lean")].replace("/", ".")


def rel_of(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def texts_sha(texts: dict) -> str:
    """One hash of a delivery's Lean files {rel (under lean/): text or None}."""
    h = hashlib.sha256()
    for rel in sorted(texts):
        t = texts[rel]
        h.update(rel.encode() + b"\0" + (b"\1" if t is None else b"\2" + t.encode()) + b"\0")
    return h.hexdigest()


def safe_rmtree(p: pathlib.Path) -> None:
    """rm -rf only below local/sets, resolved (never through a symlink into the live repository)."""
    real = pathlib.Path(os.path.realpath(p))
    base = pathlib.Path(os.path.realpath(SB))
    if real == base or base not in real.parents:
        raise RuntimeError(f"refusing to remove {p} ({real}): not below {base}")
    shutil.rmtree(real, ignore_errors=True)


def in_frozen(module: str) -> bool:
    """The frozen tree has a compiled version of `module`."""
    return (PUBLIB / module.replace(".", "/")).with_suffix(".olean").is_file()


# ---------------------------------------------------------------- judgement (rule 1: the review agent decides)

def eligible(j: dict | None) -> bool | None:
    """True: statement-preserving and downstream-unaffected; False: not; None: no usable judgement."""
    if not isinstance(j, dict):
        return None
    su, da = j.get("statement_unchanged"), j.get("downstream_affected")
    if not isinstance(su, bool) or not isinstance(da, bool):
        return None
    return su and not da


def reviewer_judgement(head: str) -> dict | None:
    """The cc reviewer's `interface` field of this head's verdict (stage 3), when the delivery was read."""
    v = read_json(ROOT / "local" / "verdicts" / "3" / f"{head}.json") or {}
    j = v.get("interface")
    if isinstance(j, dict) and eligible(j) is not None and v.get("verdict") in ("PASS", "FIX"):
        return dict(j, source="reviewer", reviewer_verdict=v.get("verdict"))
    return None


def parse_judgement(text: str) -> dict | None:
    dec = json.JSONDecoder()
    for m in reversed(list(re.finditer(r"\{\s*\"statement_unchanged\"", text or ""))):
        try:
            v = dec.raw_decode(text[m.start():])[0]
        except ValueError:
            continue
        if eligible(v) is not None:
            return v
    return None


def importers(module: str, limit: int = 40) -> list[str]:
    out = git("grep", "-l", "-E", rf"^(public +)?(meta +)?import +(all +)?{re.escape(module)}\s*$", "HEAD", "--", "lean/")
    mods = sorted({module_of(p.split(":", 1)[1][len("lean/"):]) for p in out.split() if p.endswith(".lean") and ":" in p})
    return mods[:limit] + ([f"... {len(mods) - limit} more"] if len(mods) > limit else [])


JUDGE_PROMPT = """You are the review agent who decides one question about ONE delivery of the Lean project weil-conjectures-sheaf
(group {g}, item {item}, branch deliver/{g}/{item} at {head}). You judge only; you write no file except your answer.

The question (the owner's rule, 2026-10-28): does this delivery leave every statement and the public interface of the
library unchanged, so that no module outside the delivery can be affected? If yes, the delivery is verified by
compiling its own modules on the frozen library and is done at once, before the global build; if no, it takes the
ordinary path and waits for the global build. A wrong "yes" lets a broken interface through until the global build.

Judge both:
  statement_unchanged: every existing declaration keeps its statement (name, binders, universes, type), every
    existing definition keeps its body and its transparency (`@[irreducible]`, `@[reducible]`, `@[expose]`, `abbrev`),
    no declaration is removed or renamed, no instance, `simp`/`ext`/other attribute, `notation`, `macro`, or `public
    import` of an existing module changes, and no file-level `variable`/`open`/`set_option`/local attribute changes
    how an existing PUBLIC statement or definition elaborates (one that can only affect proofs is fine; say which).
    A changed proof is fine.
  downstream_affected: could any module that imports a delivered module (directly or through other modules) compile
    differently? Think of: new public declarations in an EXISTING module (a name clash with a declaration of an
    importer, a new instance or simp lemma, a new coercion), new or removed `public import`s (they change what
    importers see, including instances), changed definitions, `@[expose]` sections, `private`/`protected` changes.
    A NEW module that no existing module imports cannot affect downstream; the item's module changing only proofs
    cannot either.
Edge cases count against "unchanged": when unsure, answer statement_unchanged false or downstream_affected true.

Below are the delivered Lean files as unified diffs against the main branch, the direct importers of each changed
existing module, and the mechanical interface comparison of tools/leanindex.py. That comparison is REFERENCE ONLY:
our practice shows it often errs in both directions (it flags proof-only changes of sections and attributes, it misses
new public imports and instances); decide from the diffs. You may read the repository at {repo} (read-only, branch
sheaf-dag) to look at an importer or a declaration; do not compile.

{body}

{evidence}

Answer with your reasoning in a few sentences, then ONE line of JSON and nothing after it:
{{"statement_unchanged": true or false, "downstream_affected": true or false, "new_public_declarations": ["<names in existing modules>"], "reasoning": "<one paragraph>"}}"""


def judge_body(D_mods: list[dict]) -> str:
    """The diffs, importers and mechanical comparison of the delivered modules (read_delivery's module list)."""
    import difflib
    parts, total = [], 0
    for m in D_mods:
        old, new = m.get("old") or "", m.get("text")
        rel = m["file"]
        if new is None:
            parts.append(f"### {rel}: DELETED"); continue
        if not old:
            head = f"### {rel}: NEW module (role {m.get('role')})"
            diff = new
        else:
            head = f"### {rel}: changed (role {m.get('role')}); direct importers: {', '.join(importers(m['module'])) or 'none'}"
            diff = "".join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), "main/" + rel, "delivery/" + rel, n=3))
        try:
            mech = li.interface_changes(old, new) if old else ["(new module)"]
        except Exception as e:  # noqa: BLE001
            mech = [f"(comparison failed: {e!r})"]
        if len(diff) > 60000:
            diff = diff[:60000] + f"\n... ({len(diff) - 60000} more characters; read the file on the branch)"
        total += len(diff)
        parts.append(f"{head}\nmechanical comparison (reference only): {'; '.join(mech) or 'no interface change found'}\n```diff\n{diff}\n```")
        if total > 200000:
            parts.append("(further files omitted; read them with `git show <head>:<path>`)"); break
    return "\n\n".join(parts)




# ---------------------------------------------------------------- the frozen tree's version (publish generation)

GEN = ROOT / "local" / "builds" / "publish-gen"


def pub_gen() -> tuple[int, str]:
    """(N, 'publishing'|'done') written by tools/build.py around a publish (publish(): "N publishing" before the
    rsync; finish_result: "N done" after published.json). No file yet: (0, 'done')."""
    try:
        n, st = GEN.read_text().split()[:2]
        return int(n), st
    except (OSError, ValueError):
        return 0, "done"


def frozen_version(wait: float = 600) -> dict | None:
    """The frozen tree's version when no publish is in progress: {gen, commit, time}; None after `wait` seconds of
    publishing, or when the published commit is unknown."""
    t0 = time.time()
    while True:
        n, st = pub_gen()
        pub = published()
        if st == "done" and not (ROOT / "local" / "PUBLISHING").exists() and pub.get("commit"):
            return {"gen": n, "commit": pub["commit"], "time": pub.get("time")}
        if time.time() - t0 > wait:
            return None
        time.sleep(5)


def same_version(v: dict) -> bool:
    n, st = pub_gen()
    return st == "done" and n == v["gen"] and published().get("commit") == v["commit"] \
        and not (ROOT / "local" / "PUBLISHING").exists()


# ---------------------------------------------------------------- the compiles of one set

def lake_options(module: str) -> dict:
    """The options Lake gives Lean for `module` (its setup.json): the package's [leanOptions] and its library's own
    (lakefile.toml; the Sheaf library adds autoImplicit = false). With them, the package name and isModule, a compile
    here writes the same .olean as Lake's (measured 2026-10-28: byte-identical .olean/.olean.server/.olean.private)."""
    import tomllib
    cfg = tomllib.loads((LEAN / "lakefile.toml").read_text())

    def flat(d, pre=""):        # TOML reads `pp.unicode.fun = true` as nested tables; Lean wants the dotted name
        out = {}
        for k, x in (d or {}).items():
            if isinstance(x, dict):
                out.update(flat(x, pre + k + "."))
            else:
                out[pre + k] = x
        return out
    opts = flat(cfg.get("leanOptions"))
    top = module.split(".")[0]
    for lib in cfg.get("lean_lib") or []:
        if lib.get("name") == top or top in [r.split(".")[0] for r in lib.get("roots") or []]:
            opts.update(flat(lib.get("leanOptions")))
            break
    return opts


def lake_package() -> str:
    import tomllib
    return tomllib.loads((LEAN / "lakefile.toml").read_text()).get("name") or "weil-conjectures"


def is_module_file(text: str) -> bool:
    """The file opens with `module` (the module system), after comments."""
    t = _COMMENT.sub("", text or "").lstrip()
    return bool(re.match(r"module\b", t))


def setup_json(name: str, module_file: bool, arts: dict) -> str:
    return json.dumps({"name": name, "isModule": module_file, "package": lake_package(), "options": lake_options(name),
                       "importArts": arts, "dynlibs": [], "plugins": []})


def packages_path() -> list[str]:
    return sorted(str(x) for x in (LEAN / ".lake" / "packages").glob("*/.lake/build/lib/lean"))


def frozen_path() -> list[str]:
    return [str(PUBLIB)] + packages_path()


def newlib() -> pathlib.Path:
    """local/sets/_new/lib/lean: the new modules of the valid passed sets, for the WORKERS' compiles only
    (tools/remote_compile_set.py hands them to Lean by importArts). Set builds never use it (review item 4)."""
    return NEWLINK / "lib" / "lean"


def imports_of(text: str) -> list[str]:
    import import_cycles as ic
    return sorted(ic.imports(text or ""))


def order_new(texts: dict, new: list[str]) -> list[str]:
    """The new modules in an order where each comes after the new modules it imports."""
    deps = {m: [d for d in imports_of(texts[rel_of(m)]) if d in new and d != m] for m in new}
    out, seen = [], set()

    def visit(m, stack=()):
        if m in seen or m in stack:
            return
        for d in deps[m]:
            visit(d, stack + (m,))
        seen.add(m); out.append(m)
    for m in sorted(new):
        visit(m)
    return out


def arts_of(top: pathlib.Path, module: str) -> list | None:
    """Lean's importArts entry of a compiled module under `top` ([[.olean, .olean.server, .olean.private], [.ir.sig,
    .ir]]; as tools/remote_compile_set.py), None when it has no .olean there."""
    o = (top / module.replace(".", "/")).with_suffix(".olean")
    if not o.is_file():
        return None
    ol = [str(o)]
    for s in (".olean.server", ".olean.private"):
        q = o.with_suffix(s)
        if not q.is_file():
            break
        ol.append(str(q))
    ir = []
    for s in (".ir.sig", ".ir"):
        q = o.with_suffix(s)
        if not q.is_file():
            break
        ir.append(str(q))
    return [ol, ir]


def import_arts(dirs: list[pathlib.Path], modules) -> dict:
    """{module: arts} for the compiled modules found in `dirs` (the first wins). Lean finds a module by the first
    LEAN_PATH root that has its top directory (Sheaf/), so a set's own compiled modules cannot simply be put on
    LEAN_PATH next to the frozen tree: they are handed to Lean one by one (--setup importArts); the frozen tree and the
    packages stay the LEAN_PATH."""
    out = {}
    for m in modules:
        for d in dirs:
            a = arts_of(d, m)
            if a:
                out[m] = a
                break
    return out


ACCEPT = 60      # seconds: a single file compiles alone within 60 s (the owner's acceptance bar)


def compile_one(folder: pathlib.Path, module: str, outdir: pathlib.Path | None, arts: dict, name: str | None = None,
                root: str = "src") -> dict:
    """lean -j1 of `module`'s source under <folder>/<root> against the frozen tree, with the compiled modules `arts`
    (importArts) in front; writes .olean/.ilean (and .olean.server/.olean.private/.ir) to `outdir` when given.
    Over ACCEPT seconds is a failure (Lean may run up to SHEAF_FILE_RUN_LIMIT so that its messages arrive).
    {rc, secs, out, errors, slow}."""
    rel = rel_of(module)
    cmd = ["nice", "-n", "0", LEANBIN, "-j1", "-R", str(folder / root)]
    if outdir is not None:
        o = outdir / rel[:-len(".lean")]
        o.parent.mkdir(parents=True, exist_ok=True)
        for x in o.parent.glob(o.name + ".*"):
            x.unlink()
        cmd += ["-o", str(o) + ".olean", "-i", str(o) + ".ilean"]
    arts = {m: a for m, a in arts.items() if m != module}
    # as Lake calls Lean (its setup.json: name, isModule, package, options); the set's own compiled modules as importArts
    sf = folder / f"setup-{name or module}.json"
    sf.write_text(setup_json(module, is_module_file((folder / root / rel).read_text(errors="ignore")), arts))
    cmd += ["--setup", str(sf)]
    limit = max(ACCEPT, int(setting("SHEAF_FILE_RUN_LIMIT", "120")))
    t0 = time.time()
    try:
        p = subprocess.run(cmd + [str(folder / root / rel)], cwd=folder, capture_output=True, text=True, timeout=limit,
                           env=dict(os.environ, LEAN_PATH=":".join(frozen_path()), LEAN_NUM_THREADS="1"))
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        so = e.stdout.decode(errors="ignore") if isinstance(e.stdout, bytes) else (e.stdout or "")
        rc, out = 124, so + f"\n(stopped after {limit} s)"
    secs = round(time.time() - t0, 1)
    errs = [l for l in out.splitlines() if re.search(r":\d+:\d+: error", l) or l.startswith("error")]
    rc = rc if (rc or not errs) else 1
    slow = secs > ACCEPT
    if slow and not rc:
        rc = 124
        errs = errs + [f"took {secs} s > {ACCEPT} s: not acceptable (a single file compiles alone within {ACCEPT} s)"]
    return {"rc": rc, "secs": secs, "out": out[-6000:], "errors": errs[:20], "slow": slow}


# The probe: for every constant of each probed module, the axioms beyond the three allowed and sorryAx (transitively),
# the constants whose own term uses sorryAx, and every non-internal constant's name (to check that each declaration of
# the source was compiled: no `#exit`, nothing skipped). After tools/build.py BATCH_PROBE.
PROBE = """
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : List Name := [%s]
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  for m in mods do
    let some idx := env.getModuleIdx? m | logInfo m!"SHEAF-MISSING {m}"
    let mut cnt : Nat := 0
    for c in env.header.moduleData[idx.toNat]!.constNames do
      let some ci := env.find? c | continue
      let used := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true)).elim #[] (·.getUsedConstants)
      if used.contains ``sorryAx then logInfo m!"SHEAF-SORRY {m} {c}"
      if c.isInternal then continue
      cnt := cnt + 1
      logInfo m!"SHEAF-CONST {m} {c}"
      for a in (← Lean.collectAxioms c) do
        unless ok.contains a do logInfo m!"SHEAF-AXIOM {m} {c} {a}"
    logInfo m!"SHEAF-PROBED {m} {cnt}"
"""


def run_probe(folder: pathlib.Path, mods: list[str], arts: dict) -> tuple[dict, str]:
    """{module: {probed, sorry, axioms, consts}} for the set's compiled modules. A module-system file with `import all`
    of the probed modules: their proof bodies are loaded (a plain public import shows no `sorry` inside proofs) and the
    private declarations of their imports are not (no twin-module collision of a non-module probe file). One run over
    all; a module the common run did not reach is probed alone."""
    def one(ms, name):
        f = folder / "src" / f"{name}.lean"
        f.write_text("module\nimport Lean.Elab.Command\n" + "".join(f"import all {m}\n" for m in ms)
                     + PROBE % ",\n    ".join("`" + m for m in ms))
        sf = folder / f"setup-{name}.json"
        sf.write_text(json.dumps({"name": name, "isModule": True, "package": lake_package(), "options": {},
                                  "importArts": arts, "dynlibs": [], "plugins": []}))
        try:
            p = subprocess.run([LEANBIN, "--setup", str(sf), "-R", str(folder / "src"), str(f)], cwd=folder,
                               capture_output=True, text=True, timeout=600,
                               env=dict(os.environ, LEAN_PATH=":".join(frozen_path()), LEAN_NUM_THREADS="1"))
            out = p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            out = "(probe stopped after 600 s)"
        f.unlink(missing_ok=True)
        return {m: {"probed": bool(re.search(r"SHEAF-PROBED " + re.escape(m) + r" \d+", out)),
                    "sorry": re.findall(r"SHEAF-SORRY " + re.escape(m) + r" (\S+)", out),
                    "consts": re.findall(r"SHEAF-CONST " + re.escape(m) + r" (\S+)", out),
                    "axioms": re.findall(r"SHEAF-AXIOM " + re.escape(m) + r" (\S+) (\S+)", out)} for m in ms}, out
    res, out = one(mods, "SetProbe")
    alone = [m for m in mods if not res[m]["probed"]] if len(mods) > 1 else []
    for m in alone:
        r1, o1 = one([m], "SetProbe_" + m.replace(".", "_"))
        res[m] = r1[m]
        out += "\n" + o1[-1500:]
    return res, out[-4000:]


def declared_missing(text: str, consts: list[str]) -> list[str]:
    """Named declarations of the source that the compiled module does not contain (a `#exit`, a skipped block)."""
    import stage3_delivery as s3
    names = set(consts)
    out = []
    for key, d in s3.decl_table(text or "").items():
        n = (d.get("name") or "").removeprefix("_root_.")
        if not n or d.get("kw") in ("example",) or d.get("private"):
            continue
        if not any(c == n or c.endswith("." + n) for c in names):
            out.append(n)
    return out


EXIT = re.compile(r"^\s*#exit\b", re.M)
_COMMENT = re.compile(r"--[^\n]*|/-.*?-/", re.S)


def has_exit(text: str) -> bool:
    return bool(EXIT.search(_COMMENT.sub("", text or "")))


_GRAPH: dict = {}


def library_graph() -> dict:
    """{module: imports} of the library's Sheaf and WeilConjectures modules (the live sources; kept 10 min)."""
    if _GRAPH.get("t", 0) > time.time() - 600:
        return _GRAPH["g"]
    import import_cycles as ic
    scan = ic._memo_imports()
    g = {}
    for top in ("Sheaf", "WeilConjectures"):
        for d, _, fs in os.walk(LEAN / top):
            for x in fs:
                if x.endswith(".lean"):
                    p = os.path.join(d, x)
                    try:
                        g[module_of(os.path.relpath(p, LEAN))] = set(scan(open(p, errors="ignore").read()))
                    except OSError:
                        pass
    _GRAPH.update(t=time.time(), g=g)
    return g


def intermediates(texts: dict, changed: list[str]) -> list[str]:
    """The unchanged modules on an import path from one changed module of the set to another (as ~/cc1/between.py
    counts them), in an order where each comes after the others it imports."""
    g = dict(library_graph())
    for rel, t in texts.items():
        g[module_of(rel)] = set(imports_of(t))
    S = set(changed)
    reach = set()
    todo = [i for m in S for i in g.get(m, ())]
    while todo:
        x = todo.pop()
        if x in reach or x not in g:
            continue
        reach.add(x)
        todo += list(g.get(x, ()))
    rev = {}
    for x in reach | S:
        for i in g.get(x, ()):
            rev.setdefault(i, set()).add(x)
    up, todo = set(), list(S)
    while todo:
        x = todo.pop()
        for y in rev.get(x, ()):
            if y in reach and y not in S and y not in up:
                up.add(y); todo.append(y)
    out, seen = [], set()

    def visit(m, stack=()):
        if m in seen or m in stack:
            return
        for d in g.get(m, ()):
            if d in up:
                visit(d, stack + (m,))
        seen.add(m); out.append(m)
    for m in sorted(up):
        visit(m)
    return out


def compile_intermediates(folder: pathlib.Path, inter: list[str], commit: str, changed: list[str], new: list[str],
                          compiles: dict) -> bool:
    """The intermediates from their frozen sources (the published commit), against the set's changed modules, in
    import order, into <folder>/inter/."""
    for m in inter:
        data = subprocess.run(["git", "show", f"{commit}:lean/{rel_of(m)}"], cwd=ROOT, capture_output=True).stdout
        p = folder / "isrc" / rel_of(m)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
    for m in inter:
        arts = import_arts([folder / "changed", folder / "inter", folder / "new"], set(changed) | set(inter) | set(new))
        c = compile_one(folder, m, folder / "inter", arts, name=m + "-inter", root="isrc")
        compiles["(intermediate) " + m] = c
        if c["rc"]:
            return False
    return True


def set_id(g: str, item: str, head: str, sha: str, v: dict) -> str:
    """Immutable: one folder per head, texts and frozen version; never rebuilt in place once complete."""
    return f"{g}__{item}__{head[:12]}__{sha[:8]}__g{v['gen']}-{v['commit'][:8]}"


def sid_lock(sid: str):
    d = SB / "locks"
    d.mkdir(parents=True, exist_ok=True)
    f = open(d / f"{sid}.lock", "w")
    fcntl.flock(f, fcntl.LOCK_EX)
    return f


def mem_available_gb() -> float:
    try:
        for l in open("/proc/meminfo"):
            if l.startswith("MemAvailable:"):
                return int(l.split()[1]) / 1048576
    except OSError:
        pass
    return 1e9


def build_set(g: str, item: str, head: str, texts: dict, allowed: dict, v: dict) -> dict:
    """Compile the set `texts` {rel under lean/: text} of one delivery on the frozen tree version `v` (the rules at
    the top). The folder local/sets/<id>/ keeps sources, compiled modules and set.json; a complete folder is never
    rebuilt (its set.json is returned)."""
    t0 = time.time()
    sha = texts_sha(texts)
    sid = set_id(g, item, head, sha, v)
    folder = SB / sid
    lk = sid_lock(sid)
    try:
        done = read_json(folder / "set.json")
        # a complete result is final; over 60 s under load ("slow") and infrastructure faults are tried again
        if done and done.get("sha") == sha and done.get("phase") not in ("infra", "slow"):
            return done
        res = {"id": sid, "folder": str(folder), "group": g, "item": item, "head": head, "sha": sha,
               "base": v["commit"], "base_gen": v["gen"], "base_time": v.get("time"),
               "time": time.strftime("%FT%TZ", time.gmtime())}
        mods = sorted(module_of(r) for r in texts)
        if folder.exists():
            safe_rmtree(folder)             # an incomplete attempt of this very id (no set.json)
        folder.mkdir(parents=True)
        # the elan proxy chooses the toolchain by the lean-toolchain file of the working directory: the library's
        shutil.copy2(LEAN / "lean-toolchain", folder / "lean-toolchain")
        for rel, text in texts.items():
            p = folder / "src" / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        new = [m for m in mods if not in_frozen(m)]
        changed = [m for m in mods if m not in new]
        res.update(modules=mods, new_modules=new, changed_modules=changed)
        compiles = {}
        for m in order_new(texts, new):                  # new modules first, each seeing the set's earlier ones
            c = compile_one(folder, m, folder / "new", import_arts([folder / "new"], new))
            compiles[m] = c
            if c["rc"]:
                break
        failed = [m for m, c in compiles.items() if c["rc"]]
        if not failed:                                    # then every changed module against the frozen tree alone
            arts = import_arts([folder / "new"], new)
            par = int(setting("SHEAF_SETBUILD_PAR", "4"))
            with cf.ThreadPoolExecutor(max_workers=max(1, par)) as ex:
                for m, c in zip(changed, ex.map(lambda x: compile_one(folder, x, folder / "changed", arts), changed)):
                    compiles[m] = c
            failed = [m for m, c in compiles.items() if c["rc"]]
        if failed and all(m in changed for m in failed) and len(changed) > 1 and not any(compiles[m]["slow"] for m in failed):
            # rule 4 and the intermediates (~/cc1/between.py: 97.8 % of deliveries have none; review item 2): a changed
            # module that compiles only with the set's other changed modules (directly, or through up to 10 rebuilt
            # intermediates) shows an interface change: phase interface-changed, never a pass; more than 10
            # intermediates: interface-path. Every case is logged.
            inter = intermediates(texts, changed)
            res["intermediates"] = inter
            if inter:
                with open(SB / "intermediates.tsv", "a") as f:
                    f.write("\t".join([time.strftime("%FT%TZ", time.gmtime()), g, item, head, str(len(inter)),
                                       ",".join(failed), ",".join(inter[:30])]) + "\n")
            cross = []
            if len(inter) > 10:
                res.update(ok=False, phase="interface-path",
                           why=f"{', '.join(failed[:4])} fail(s) against the frozen tree and {len(inter)} unchanged modules lie "
                               "between changed modules of the set (more than 10): the interface path")
            else:
                if inter and not compile_intermediates(folder, inter, v["commit"], changed, new, compiles):
                    inter_ok = False
                else:
                    inter_ok = True
                if inter_ok:
                    arts = import_arts([folder / "changed", folder / "inter", folder / "new"],
                                       set(changed) | set(inter) | set(new))
                    for m in failed:
                        c2 = compile_one(folder, m, None, arts, name=m + "-cross")
                        if c2["rc"] == 0:
                            cross.append(m)
                res["cross_check"] = cross
                if cross:
                    res.update(ok=False, phase="interface-changed",
                               why=f"{', '.join(cross)} compile(s) only against the set's changed modules"
                                   + (f" (through {len(inter)} rebuilt intermediates)" if inter else "")
                                   + ", not against the frozen tree: the interface of a changed module did change")
        res["compiles"] = {m: {k: c[k] for k in ("rc", "secs", "errors", "slow")} for m, c in compiles.items()}
        res["slow"] = sorted(m for m, c in compiles.items() if c["slow"])
        (folder / "compile.log").write_text("\n\n".join(f"=== {m} rc {c['rc']} {c['secs']} s\n{c['out']}" for m, c in compiles.items()))
        if "phase" in res:
            pass
        elif failed:
            base_missing = any(re.search(r"unknown module prefix|object file .* does not exist|bad import",
                                         " ".join(compiles[m]["errors"]) + compiles[m]["out"][-2000:]) for m in failed)
            res.update(ok=False, phase="slow" if any(compiles[m]["slow"] for m in failed) else
                       ("base-missing" if base_missing else "compile"),
                       why=f"{failed[0]}: " + " | ".join(compiles[failed[0]]["errors"][:4])[:1500])
        else:
            arts = import_arts([folder / "changed", folder / "new"], mods)
            missing = [m for m in mods if m not in arts]
            if missing:              # review item 7: every probed module comes from the set's own folder
                res.update(ok=False, phase="probe", why=f"no compiled file in the set for {', '.join(missing)}")
            else:
                probe, ptail = run_probe(folder, mods, arts)
                res["probe"] = {m: {k: x[k] for k in ("probed", "sorry", "axioms")} for m, x in probe.items()}
                notrun = [m for m in mods if not probe[m]["probed"]]
                skipped = {m: declared_missing(texts[rel_of(m)], probe[m]["consts"]) for m in mods if probe[m]["probed"]}
                skipped = {m: x for m, x in skipped.items() if x}
                if notrun:
                    res.update(ok=False, phase="probe", why=f"the sorry/axiom probe did not run on {', '.join(notrun)}: {ptail[-800:]}")
                elif skipped:
                    res.update(ok=False, phase="probe-findings", findings=[
                        f"{rel_of(m)}: declared but not in the compiled module: {', '.join(x[:6])}" for m, x in skipped.items()])
                else:
                    f = sorry_findings(res, allowed, texts)
                    res.update(ok=not f, phase="built" if not f else "probe-findings", findings=f)
                # reference evidence for the judgement: is the public .olean of each changed module byte-identical?
                res["public_olean_identical"] = {
                    m: _same_file(folder / "changed" / (m.replace(".", "/") + ".olean"),
                                  PUBLIB / (m.replace(".", "/") + ".olean")) for m in changed}
        if not same_version(v):
            res.update(ok=False, phase="infra", why="the frozen tree was republished during the set build")
        res["seconds"] = round(time.time() - t0)
        res["allowed_sorry"] = allowed
        write_json(folder / "set.json", res)
        return res
    finally:
        lk.close()


def _same_file(a: pathlib.Path, b: pathlib.Path) -> bool:
    try:
        if a.stat().st_size != b.stat().st_size:
            return False
        with open(a, "rb") as fa, open(b, "rb") as fb:
            while True:
                x, y = fa.read(1 << 20), fb.read(1 << 20)
                if x != y:
                    return False
                if not x:
                    return True
    except OSError:
        return False


def sorry_findings(res: dict, allowed: dict, texts: dict) -> list[str]:
    """The probe's `sorry` beyond what the delivery may leave (tools/batch_land.py land_one: sorry_allowed) and the
    axioms beyond propext, Classical.choice, Quot.sound; as tools/build.py batch_checks reads them."""
    import stage3_delivery as s3
    out = []
    for m, pr in (res.get("probe") or {}).items():
        rel = rel_of(m)
        for decl, a in sorted(set(map(tuple, pr.get("axioms") or []))):
            out.append(f"{rel}: {decl} uses the axiom {a}")
        table = s3.decl_table(texts.get(rel) or "")
        extra = sorted({s3.owner(c, table) for c in pr.get("sorry") or []} - set(allowed.get(m) or []))
        if extra:
            out.append(f"{rel}: `sorry` in {', '.join(extra)}, which the delivery may not leave")
    return out


def allowed_sorry(D_mods: list[dict]) -> dict:
    """As tools/batch_land.py land_one records it for the global build's probe."""
    out = {}
    for m in D_mods:
        d = m.get("diff") or {}
        out[m["module"]] = sorted(set(d.get("sorry_before") or []) - set(d.get("body_changed") or []) | set(d.get("new_sorry") or []))
    return out


# ---------------------------------------------------------------- deliveries

def fix_overrides(head: str, D_mods: list[dict]) -> dict:
    """A reviewer's FIX: its corrected Lean files (local/verdicts/3/<head>/fixes/<base name>) replace the delivered ones,
    as tools/merge_delivery.py --apply-fixes lands them."""
    v = read_json(ROOT / "local" / "verdicts" / "3" / f"{head}.json") or {}
    fx = ROOT / "local" / "verdicts" / "3" / head / "fixes"
    if v.get("verdict") != "FIX" or not fx.is_dir():
        return {}
    names = {p.name: p for p in fx.iterdir() if p.is_file() and p.suffix == ".lean"}
    return {m["file"]: names[pathlib.PurePosixPath(m["file"]).name].read_text()
            for m in D_mods if pathlib.PurePosixPath(m["file"]).name in names}


def delivery(g: str, item: str, head: str | None = None) -> dict | None:
    """The delivery on its branch, read as the lander reads it (tools/stage3_delivery.py read_delivery), with a
    reviewer's fixed files in place."""
    import stage2_delivery as s2
    import stage3_delivery as s3
    head = head or branch_head(g, item)
    if not head:
        return None
    base = git("merge-base", "sheaf-dag", head).strip()
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item)
    over = fix_overrides(head, D["modules"])
    if over:
        D = s3.read_delivery(s2.Git(ROOT), head, base, g, item, overrides=over)
    texts = {m["file"][len("lean/"):]: m["text"] for m in D["modules"] if m["file"].startswith("lean/")}
    return {"group": g, "item": item, "head": head, "D": D, "texts": texts, "sha": texts_sha(texts), "fixed": sorted(over),
            "roles": sorted({str(m.get("role")) for m in D["modules"]}), "fails": D["fails"]}


def branch_head(g: str, item: str) -> str:
    return git("rev-parse", "-q", "--verify", f"refs/heads/deliver/{g}/{item}").strip()


def candidates() -> list[tuple[str, str, str]]:
    """(group, item, head) of the stage-3 delivery branches whose group holds the claim (the lander's candidates)."""
    import stage3_delivery as s3
    out = []
    for ref in git("for-each-ref", "--format=%(refname:short) %(objectname)", "refs/heads/deliver").splitlines():
        try:
            name, head = ref.split()
        except ValueError:
            continue
        p = name.split("/")
        if len(p) != 3 or not s3.is_stage3_item(p[2]):
            continue
        g, item = p[1], p[2]
        if (read_json(ROOT / "coord" / "claims" / f"{item}.lock") or {}).get("who") != g:
            continue
        out.append((g, item, head))
    return out


def needs_reader(g: str, item: str, D: dict) -> str | None:
    """The class reason when the cc review service reads this delivery (tools/review_class.py), else None."""
    import review_class as rc
    try:
        cl, why, _h = rc.classify(g, item, D)
    except Exception as e:  # noqa: BLE001
        return f"class unknown ({e!r})"[:200]
    return None if cl == "AUTO" else f"{cl}: {why}"[:300]


def verdict_of(head: str) -> dict:
    return read_json(ROOT / "local" / "verdicts" / "3" / f"{head}.json") or {}


def gates(dv: dict, v: dict) -> tuple[str, str] | None:
    """The lander's honesty gates that need no compile (review item 3; as tools/batch_land.py check): the static checks
    of read_delivery, no `#exit`, sorry_ledger.missing_gate (admits, hollow data or instance fields, unattributable
    holes, new axioms), no import cycle closed, every import present in the FROZEN tree or the set (an import of a
    module the frozen tree does not have yet, another set's new module included, waits: review item 4).
    (phase, why) when the delivery cannot pass now, else None."""
    import import_cycles as cycles
    import sorry_ledger as sl
    D = dv["D"]
    if D["fails"]:
        return "static", "; ".join(f"({L}) {x}" for L, x in D["fails"][:4])
    if set(dv["roles"]) - {"item", "new", "adapted"}:
        return "not-eligible", f"roles {', '.join(dv['roles'])}"
    outside = [r for r in dv["texts"] if not module_of(r).startswith(PROJECT)]
    if outside or not dv["texts"]:
        return "not-eligible", f"files outside the library modules: {' '.join(outside) or '-'}"
    for m in D["modules"]:
        if m["text"] is None:
            return "not-eligible", "the delivery deletes a module"
        if has_exit(m["text"]):
            return "static", f"{m['file']}: #exit"
        miss = sl.missing_gate(m.get("old"), m["text"])
        if miss:
            return "static", m["file"] + ": " + "; ".join(miss[:4])
    texts = {m["module"]: m["text"] for m in D["modules"]}
    cyc = cycles.closing_cycle(library_graph(), texts)
    if cyc:
        return "static", "import cycle: " + " -> ".join(cyc)
    try:
        cycles.refuse_missing(texts, cycles.source_modules(ROOT, v["commit"]), cycles.source_roots(LEAN))
    except RuntimeError as e:
        return "wait-dependency", f"imports a module the frozen tree does not have yet: {str(e)[:400]}"
    return None


def judge_evidence(r: dict) -> str:
    if not r.get("compiles"):
        return ""
    lines = ["Compiler evidence (reference only, it does not decide): each changed module was compiled alone against "
             "the frozen library (the other changed modules of the delivery in their OLD version)."]
    for m, c in (r.get("compiles") or {}).items():
        lines.append(f"- {m}: {'compiles' if not c['rc'] else 'FAILS: ' + ' | '.join(c['errors'][:2])[:400]}")
    for m, same in (r.get("public_olean_identical") or {}).items():
        lines.append(f"- {m}: compiled public .olean (statements, definitions, instances, attributes as exported) is "
                     f"{'BYTE-IDENTICAL to' if same else 'different from'} the frozen one")
    return "\n".join(lines)


def judgement(head: str, sha: str) -> dict | None:
    """The reviewer's `interface` field of this head's PASS/FIX verdict, else our own judgement of these texts."""
    return reviewer_judgement(head) or read_json(JUDGE / f"{head}__{sha[:12]}.json")


def run_judge(g: str, item: str, head: str, sha: str, D_mods: list[dict], evidence: str) -> dict | None:
    """One judgement session; stored in local/sets/judge/<head>__<sha12>.json."""
    sys.path.insert(0, str(SVC))
    import tokenpool as tp  # noqa: E402
    d = JUDGE / f"{head}__{sha[:12]}"
    d.mkdir(parents=True, exist_ok=True)
    prompt = JUDGE_PROMPT.format(g=g, item=item, head=head[:12], repo=SVC / "clones" / "live", body=judge_body(D_mods),
                                 evidence=evidence or "(no compile evidence)")
    (d / "prompt.txt").write_text(prompt)
    model = (tp.config() or {}).get("model") or "claude-opus-5-5"
    t0 = time.time()
    kind, detail, obj, _lease = tp.run_claude(prompt, str(d), f"J:{g}/{item}", model=model,
                                              timeout=int(setting("SHEAF_SETBUILD_JUDGE_TIMEOUT", "900")),
                                              out_path=str(d / "out.json"), err_path=str(d / "err.txt"))
    if kind != "ok":
        log("judge", g, item, head[:9], "no answer:", kind, str(detail)[:200])
        return None
    v = parse_judgement(str((obj or {}).get("result", "")))
    if not v:
        log("judge", g, item, head[:9], "no parsable judgement")
        return None
    v = dict(v, source="judge", head=head, sha=sha, group=g, item=item, seconds=round(time.time() - t0),
             cost=(obj or {}).get("total_cost_usd"), time=time.strftime("%FT%TZ", time.gmtime()))
    write_json(JUDGE / f"{head}__{sha[:12]}.json", v)
    log("judge", g, item, head[:9], "eligible" if eligible(v) else "NOT eligible", f"{v['seconds']} s",
        str(v.get("reasoning", ""))[:160].replace("\n", " "))
    return v


def build_slot():
    """One of SHEAF_SETBUILD_SETS machine-wide slots for a set build (flock on local/sets/slots/<i>.lock); waits
    while MemAvailable is under SHEAF_SETBUILD_MIN_MEM_GB (60: 3 sets x 4 Lean + a probe stay well inside it)."""
    n = max(1, int(setting("SHEAF_SETBUILD_SETS", "3")))
    floor = float(setting("SHEAF_SETBUILD_MIN_MEM_GB", "60"))
    d = SB / "slots"
    d.mkdir(parents=True, exist_ok=True)
    while True:
        if mem_available_gb() >= floor:
            for i in range(n):
                f = open(d / f"{i}.lock", "w")
                try:
                    fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    return f
                except OSError:
                    f.close()
        time.sleep(3)


def evaluate(g: str, item: str, head: str, judge: bool = True) -> dict:
    """Gates, the set build, then the judgement (with the compile as reference evidence). Pass = the set build passed
    and the review agent judged the delivery statement-preserving and downstream-unaffected. The latest result is
    local/sets/results/<head>.json; in mode `on` a pass is recorded (record_passed), anything else revokes an earlier
    pass of this head."""
    dv = delivery(g, item, head)
    if dv is None:
        return {"head": head, "ok": False, "phase": "gone"}
    texts, sha = dv["texts"], dv["sha"]
    v = frozen_version()
    base = {"head": head, "group": g, "item": item, "sha": sha, "roles": dv["roles"], "fixed": dv["fixed"],
            "time": time.strftime("%FT%TZ", time.gmtime())}

    def done(r):
        write_json(RESULTS / f"{head}.json", r)
        if not r.get("ok") and r.get("phase") not in ("wait-reader", "no-judgement", "infra", "slow"):
            revoke(head, f"latest evaluation: {r.get('phase')}")
        log(g, item, head[:9], r.get("phase"), "PASS" if r.get("ok") else "-", f"{r.get('seconds', 0)} s",
            str(r.get("why") or "; ".join(r.get("findings") or []))[:240].replace("\n", " "))
        return r
    if v is None:
        return dict(base, ok=False, phase="infra", why="the frozen tree is being published (or unknown)")
    base.update(base=v["commit"], base_gen=v["gen"], base_time=v.get("time"))
    vd = verdict_of(head)
    if vd.get("verdict") == "RETURN":
        return done(dict(base, ok=False, phase="returned", why="the reviewer returned this head"))
    stop = gates(dv, v)
    if stop:
        return done(dict(base, ok=False, phase=stop[0], why=stop[1]))
    j = judgement(head, sha)
    if j is None and not vd:
        reader = needs_reader(g, item, dv["D"])
        if reader:
            return dict(base, ok=False, phase="wait-reader", why=reader)   # the reviewer's verdict will carry it
    allowed = allowed_sorry(dv["D"]["modules"])
    slot = build_slot()
    try:
        r = build_set(g, item, head, texts, allowed, v)
    finally:
        slot.close()
    r = dict(base, **{k: x for k, x in r.items() if k not in ("time",)})
    if r.get("phase") == "infra":
        return r
    if j is None:
        if not judge:
            return dict(r, ok=False, phase="no-judgement", built=r.get("phase"))
        j = run_judge(g, item, head, sha, dv["D"]["modules"], judge_evidence(r))
        if j is None:
            return dict(r, ok=False, phase="no-judgement", built=r.get("phase"))
    r["judgement"] = {k: j.get(k) for k in ("statement_unchanged", "downstream_affected", "source", "reasoning",
                                             "new_public_declarations")}
    if r.get("phase") == "interface-changed" and eligible(j):
        with open(SB / "judgement-wrong.tsv", "a") as f:
            f.write("\t".join([time.strftime("%FT%TZ", time.gmtime()), g, item, head, str(j.get("source")),
                               ",".join(r.get("cross_check") or []), str(len(r.get("intermediates") or []))]) + "\n")
    if r.get("ok") and not eligible(j):
        r.update(ok=False, phase="not-eligible", built="built",
                 why="the set compiles, but the review agent judged it statement-changing or downstream-affecting")
    write_json(pathlib.Path(r["folder"]) / "evaluation.json", r)
    if r.get("ok") and mode() == "on":
        why = record_passed(r)
        if why:
            r.update(ok=False, phase="not-recorded", why=why)
    return done(r)


# ---------------------------------------------------------------- passed sets

def valid_pass(rec: dict, check_head: bool = True) -> str | None:
    """None when a passed record still holds (review items 1 and 5): the switch is on, the head is still the branch
    head, the verdict is not RETURN, the latest result of the head is a pass of the same texts, the judgement (the
    reviewer's, when it came from the reviewer) is still eligible. Else the reason."""
    if mode() != "on":
        return "switch not on"
    head = rec.get("head", "")
    if check_head and branch_head(rec.get("group", ""), rec.get("item", "")) != head:
        return "the branch head moved"
    vd = verdict_of(head)
    if vd.get("verdict") == "RETURN":
        return "the reviewer returned this head"
    last = read_json(RESULTS / f"{head}.json") or {}
    if not last.get("ok") or last.get("sha") != rec.get("sha"):
        return "the latest evaluation of this head is not a pass of the same texts"
    j = judgement(head, rec.get("sha", ""))
    if not eligible(j):
        return "the judgement is no longer eligible"
    return None


def passed_records() -> list[dict]:
    out = []
    for p in sorted(PASSED.glob("*.json")) if PASSED.is_dir() else []:
        r = read_json(p)
        if r:
            out.append(r)
    return out


def record_passed(r: dict) -> str | None:
    """The set passed: record it, mark the item done, expose its new modules. None on success, else the reason it was
    not recorded. Re-checks right before recording (review items 5 and 8)."""
    head = r["head"]
    if branch_head(r["group"], r["item"]) != head:
        return "the branch head moved"
    if verdict_of(head).get("verdict") == "RETURN":
        return "the reviewer returned this head"
    mine = set(r.get("changed_modules") or [])
    for o in passed_records():
        if o.get("head") != head and mine & set(o.get("changed_modules") or []) and valid_pass(o) is None:
            return (f"{', '.join(sorted(mine & set(o['changed_modules'])))} is changed by the passed set of "
                    f"{o.get('group')}/{o.get('item')} too (not merged yet): the later one does not pass")
    p = PASSED / f"{head}.json"
    if (read_json(p) or {}).get("sha") == r["sha"]:
        return None
    write_json(p, {k: r.get(k) for k in ("id", "folder", "group", "item", "head", "sha", "modules", "new_modules",
                                         "changed_modules", "base", "base_gen", "base_time", "judgement")}
               | {"passed": time.strftime("%FT%TZ", time.gmtime())})
    try:
        q = subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "done", "3", r["item"],
                            "--note", f"set build {r['id']} passed", "--source-dir", str(pathlib.Path(r["folder"]) / "src")],
                           cwd=ROOT, capture_output=True, text=True, timeout=300)
        rc, out = q.returncode, q.stdout + q.stderr
    except Exception as e:  # noqa: BLE001
        rc, out = 1, repr(e)
    if rc != 0:
        p.unlink(missing_ok=True)
        log("queue mark failed, pass not recorded (retried later)", r["group"], r["item"], head[:9], out[-300:])
        return "queue_mark failed: " + out[-200:]
    log("PASSED", r["group"], r["item"], head[:9], "set", r["id"], "new modules:", " ".join(r.get("new_modules") or []) or "-")
    try:
        refresh_newlib()
    except Exception as e:  # noqa: BLE001
        log("refresh of _new failed", repr(e)[:200])
    return None


def revoke(head: str, reason: str, mark: bool = True) -> None:
    """Withdraw a pass (review item 1): the record goes, the item is work again (queue_mark rework)."""
    p = PASSED / f"{head}.json"
    rec = read_json(p)
    if not rec:
        return
    p.unlink(missing_ok=True)
    if mark:
        subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "rework", "3", rec["item"],
                        "--note", f"set pass withdrawn: {reason}"[:300]], cwd=ROOT, capture_output=True, timeout=300)
    log("REVOKED", rec.get("group"), rec.get("item"), head[:9], reason)
    try:
        refresh_newlib()
    except Exception:  # noqa: BLE001
        pass


def retire_or_revoke(rec: dict, why: str) -> None:
    """A pass whose head left its branch because the delivery LANDED (the ordinary batch landing merges it; the global
    build verifies it) is retired: the record goes, the item stays done. Any other reason revokes it."""
    o = outcome(rec.get("head", "")) if why == "the branch head moved" else None
    if o and o.get("state") in ("landed", "verified"):
        (PASSED / f"{rec['head']}.json").unlink(missing_ok=True)
        log("retired (landed)", rec.get("group"), rec.get("item"), rec.get("head", "")[:9], o.get("batch"), o.get("landing"))
        return
    revoke(rec["head"], why)


def passed_heads() -> dict:
    """{head: record} of the valid passed sets."""
    if mode() != "on" or not PASSED.is_dir():
        return {}
    live = {h: (g, i) for g, i, h in candidates()}
    return {r["head"]: r for r in passed_records() if r.get("head") in live and valid_pass(r, check_head=False) is None}


def is_passed(g: str, item: str, head: str) -> bool:
    """tools/pending_deps.py, ~/cc1/queue_report.py: a valid passed set counts as a pass (its dependents are
    released); never a RETURNed head, a moved branch or changed texts."""
    if mode() != "on":
        return False
    r = read_json(PASSED / f"{head}.json")
    return bool(r) and r.get("group") == g and r.get("item") == item and valid_pass(r) is None


def landed_text_check(head: str, texts: dict) -> None:
    """tools/batch_land.py land_one (review item 9): a passed set whose delivery lands with other texts (merged
    imports, a merge agent, ...) loses its pass; the landing itself is verified by the global build as before."""
    rec = read_json(PASSED / f"{head}.json")
    if rec and texts_sha(texts) != rec.get("sha"):
        revoke(head, "the delivery landed with texts other than those of its set build", mark=False)


_SOURCES: dict = {}


def passed_sources() -> dict:
    """{module: its source in the valid passed set}; tools/own_decl.py reads a module from here first (progress and
    queue see a passed set's module as written before its merge). Kept 60 s."""
    if _SOURCES.get("t", 0) > time.time() - 60:
        return _SOURCES["s"]
    out = {}
    for r in sorted(passed_heads().values(), key=lambda r: r.get("passed", "")):
        for m in r.get("modules") or []:
            p = pathlib.Path(r["folder"]) / "src" / rel_of(m)
            if p.is_file():
                out[m] = p
    _SOURCES.update(t=time.time(), s=out)
    return out


def refresh_newlib() -> None:
    """local/sets/_new/lib/lean: symlinks to the compiled new modules of the valid passed sets that the frozen tree
    does not have yet (for the workers' compiles); rebuilt beside and switched with one rename of a symlink."""
    SB.mkdir(parents=True, exist_ok=True)
    gen = SB / f"_new.{int(time.time() * 1000)}"
    lib = gen / "lib" / "lean"
    lib.mkdir(parents=True)
    for r in sorted(passed_heads().values(), key=lambda r: r.get("passed", "")):
        for m in r.get("new_modules") or []:
            if in_frozen(m):
                continue
            src = pathlib.Path(r["folder"]) / "new" / m.replace(".", "/")
            for f in src.parent.glob(src.name + ".*"):
                dst = lib / f.relative_to(pathlib.Path(r["folder"]) / "new")
                dst.parent.mkdir(parents=True, exist_ok=True)
                if dst.is_symlink():
                    dst.unlink()
                dst.symlink_to(f)
    tmp = SB / "_new.link.tmp"
    tmp.unlink(missing_ok=True)
    tmp.symlink_to(gen.name)
    os.replace(tmp, NEWLINK)
    for d in SB.glob("_new.[0-9]*"):
        if d.resolve() != gen.resolve() and time.time() - d.stat().st_mtime > 600:
            safe_rmtree(d)


def cleanup() -> None:
    """Review item 12: set folders and judgements of heads that are no longer a branch head, and set folders of a
    live head built on an older frozen version, unless a passed record names them."""
    live = {h for _g, _i, h in candidates()}
    keep = {pathlib.Path(r.get("folder", "")).name for r in passed_records()}
    cur = frozen_version(wait=0)
    n = 0
    for d in SB.iterdir():
        if not d.is_dir() or d.name.startswith(("_", ".")) or d.name in ("results", "judge", "passed", "slots", "locks") or d.name in keep:
            continue
        parts = d.name.split("__")
        if len(parts) < 4:
            continue
        head12, ver = parts[2], parts[-1]
        stale = not any(h.startswith(head12) for h in live)
        old = cur is not None and ver != f"g{cur['gen']}-{cur['commit'][:8]}" and time.time() - d.stat().st_mtime > 6 * 3600
        if stale or old:
            safe_rmtree(d); n += 1
    for f in list(JUDGE.glob("*")) if JUDGE.is_dir() else []:
        if not any(f.name.startswith(h) for h in live):
            if f.is_dir():
                safe_rmtree(f)
            else:
                f.unlink(missing_ok=True)
            n += 1
    for f in list(RESULTS.glob("*.json")) if RESULTS.is_dir() else []:
        if f.stem not in live and time.time() - f.stat().st_mtime > 7 * 86400:
            f.unlink(missing_ok=True)
    if n:
        log(f"cleanup: {n} folder(s) or judgement(s) of gone heads removed")


# ---------------------------------------------------------------- the daemon

def evaluate_proc(g: str, item: str, head: str) -> dict:
    """evaluate() in a process (session) of its own: reading a delivery costs 10-25 s of Python and the readers keep
    module-level caches. Killed with its whole process group on timeout."""
    import signal
    p = subprocess.Popen([sys.executable, str(pathlib.Path(__file__).resolve()), "eval", g, item, head], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        so, se = p.communicate(timeout=7200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        so, se = p.communicate()
        log("eval process killed after 2 h", g, item, head[:9])
        return {"phase": "timeout"}
    for line in reversed((so or "").splitlines()):
        if line.startswith("PHASE "):
            return {"phase": line.split(" ", 1)[1]}
    log("eval process failed", g, item, head[:9], ((so or "") + (se or ""))[-400:].replace("\n", " / "))
    return {"phase": "error"}


def daemon() -> int:
    SB.mkdir(parents=True, exist_ok=True)
    lockf = open(SB / "daemon.lock", "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("another daemon runs"); return 1
    (SB / "daemon.pid").write_text(str(os.getpid()))
    log("daemon started, mode", mode())
    width = int(setting("SHEAF_SETBUILD_SETS", "3")) + int(setting("SHEAF_SETBUILD_JUDGES", "4")) + 4
    ex = cf.ThreadPoolExecutor(max_workers=width)
    running, tried, last = {}, {}, {}
    last_new = last_clean = 0.0
    while True:
        if mode() == "off":
            time.sleep(30); continue
        for h, fut in list(running.items()):
            if fut.done():
                running.pop(h)
                try:
                    last[h] = (fut.result() or {}).get("phase")
                except Exception as e:  # noqa: BLE001
                    log("evaluate failed", h[:9], repr(e)[:300])
        try:
            cands = candidates()
        except Exception as e:  # noqa: BLE001
            log("candidates failed", repr(e)[:300]); cands = []
        v = frozen_version(wait=0)
        for g, item, head in cands:
            if v is None or head in running or len(running) >= width:
                continue
            r = read_json(RESULTS / f"{head}.json")
            fresh = r and r.get("base_gen") == v["gen"] and r.get("base") == v["commit"]
            if fresh and r.get("phase") not in ("infra", "slow", "wait-reader", "no-judgement", "error", "timeout"):
                if not (r.get("phase") == "built" and r.get("ok") and mode() == "on" and valid_pass_missing(r)):
                    continue
            if time.time() - tried.get(head, 0) < 900:
                continue
            tried[head] = time.time()
            running[head] = ex.submit(evaluate_proc, g, item, head)
        try:
            live = {h for _g, _i, h in cands}
            ph = {}
            for h in live:
                k = last.get(h) or ("running" if h in running else "not yet")
                ph[k] = ph.get(k, 0) + 1
            write_json(SB / "daemon-state.json", {"time": time.strftime("%FT%TZ", time.gmtime()), "candidates": len(live),
                                                  "running": len(running), "phases": ph})
        except Exception:  # noqa: BLE001
            pass
        if mode() == "on" and time.time() - last_new > 300:
            try:
                for rec in passed_records():           # passes that stopped holding are withdrawn
                    why = valid_pass(rec)
                    if why:
                        retire_or_revoke(rec, why)
                refresh_newlib()
            except Exception as e:  # noqa: BLE001
                log("pass upkeep failed", repr(e)[:300])
            last_new = time.time()
        if time.time() - last_clean > 1800:
            try:
                cleanup()
            except Exception as e:  # noqa: BLE001
                log("cleanup failed", repr(e)[:300])
            last_clean = time.time()
        time.sleep(20)


def valid_pass_missing(r: dict) -> bool:
    """A result that passed (in shadow mode) but has no passed record yet: evaluated again to record it."""
    return not (PASSED / f"{r['head']}.json").exists()


# ---------------------------------------------------------------- reports

def outcome(head: str) -> dict | None:
    """What the ordinary path did with this head: its batch entry and the landing's result in the global build."""
    bd = ROOT / "local" / "batch"
    files = [bd / "open.json", bd / "next.json"] + sorted((bd / "closed").glob("*.json"), key=lambda p: p.stat().st_mtime)[-60:]
    for p in files:
        b = read_json(p) or {}
        for e in b.get("entries") or []:
            if e.get("head") == head:
                lid = e.get("landing") or ""
                d = read_json(ROOT / "local" / "builds" / "done" / f"{lid}.json") or {}
                return {"batch": b.get("id"), "state": e.get("state"), "why": e.get("why"), "landing": lid,
                        "landing_result": d.get("result") or ("open" if (ROOT / "local" / "builds" / "requests" / f"{lid}.json").exists() else "?")}
    return None


def report(hours: float = 48) -> int:
    cut = time.time() - hours * 3600
    cells, agree, disagree, pending = {}, 0, 0, 0
    for p in sorted(RESULTS.glob("*.json")) if RESULTS.is_dir() else []:
        if p.stat().st_mtime < cut:
            continue
        r = read_json(p) or {}
        o = outcome(r.get("head", ""))
        pred = "pass" if r.get("ok") else r.get("phase", "?")
        if not o:
            act = "not landed yet"
        elif o["state"] == "verified" or o["landing_result"] == "verified":
            act = "verified"
        elif o["state"] == "landed":
            act = "landed, build pending"
        else:
            act = f"{o['state']}"
        cells[(pred, act)] = cells.get((pred, act), 0) + 1
        if act in ("not landed yet", "landed, build pending"):
            pending += 1
        elif pred == "pass":
            if act == "verified":
                agree += 1
            else:
                disagree += 1
                print(f"DISAGREE {r.get('group')}/{r.get('item')} {r.get('head', '')[:9]}: set build passed; global path: {act} {(o or {}).get('why') or ''}"[:500])
        elif pred in ("compile", "interface-changed", "probe-findings", "slow"):
            if act == "verified":
                disagree += 1
                print(f"DISAGREE {r.get('group')}/{r.get('item')} {r.get('head', '')[:9]}: set build {pred}; global verified"[:300])
            else:
                agree += 1
    print(f"mode {mode()}; set-build results of the last {hours:g} h")
    for (pred, act), n in sorted(cells.items()):
        print(f"  set build {pred:18} ordinary path: {act:24} {n}")
    print(f"decided by the global build: {agree} agree, {disagree} disagree; {pending} not decided yet")
    return 0


def status() -> int:
    print("mode", mode(), "| frozen", frozen_version(wait=0))
    rs = [read_json(p) or {} for p in RESULTS.glob("*.json")] if RESULTS.is_dir() else []
    by = {}
    for r in rs:
        by[r.get("phase")] = by.get(r.get("phase"), 0) + 1
    print("results by phase:", json.dumps(by, sort_keys=True))
    secs = sorted(r.get("seconds") or 0 for r in rs if r.get("compiles"))
    if secs:
        print(f"set build seconds: median {secs[len(secs) // 2]}, max {secs[-1]} ({len(secs)} builds)")
    print("valid passed sets:", len(passed_heads()))
    return 0


def validate(head: str, limit: int = 4) -> dict:
    """Shadow check of a pass: up to `limit` direct importers of each changed module (frozen sources) compiled against
    the frozen tree and again with the set's changed modules in front. One that compiles against the frozen tree but
    not with the set shows that downstream IS affected."""
    r = read_json(RESULTS / f"{head}.json") or {}
    if not r.get("ok"):
        return {"head": head, "skipped": r.get("phase")}
    folder = pathlib.Path(r["folder"])
    commit = r.get("base") or published_commit()
    g = library_graph()
    changed = r.get("changed_modules") or []
    out = {}
    for x in changed:
        imps = sorted(m for m, deps in g.items() if x in deps and m not in r.get("modules", []))[:limit]
        for m in imps:
            data = subprocess.run(["git", "show", f"{commit}:lean/{rel_of(m)}"], cwd=ROOT, capture_output=True).stdout
            if not data:
                continue
            pth = folder / "vsrc" / rel_of(m)
            pth.parent.mkdir(parents=True, exist_ok=True)
            pth.write_bytes(data)
            a = compile_one(folder, m, None, {}, name=m + "-vfrozen", root="vsrc")
            b = compile_one(folder, m, None, import_arts([folder / "changed", folder / "new"], set(changed) | set(r.get("new_modules") or [])),
                            name=m + "-vset", root="vsrc")
            out[m] = {"of": x, "frozen": a["rc"], "with_set": b["rc"], "secs": [a["secs"], b["secs"]],
                      "slow": [a["slow"], b["slow"]], "errors": b["errors"][:3] if b["rc"] and not a["rc"] else []}
    # only a compile ERROR with the set counts; over 60 s under load on one side only says nothing about the interface
    bad = [m for m, x in out.items() if x["frozen"] in (0, 124) and x["with_set"] not in (0, 124)]
    res = {"head": head, "group": r.get("group"), "item": r.get("item"), "importers": out, "affected": bad}
    write_json(folder / "validate.json", res)
    return res


def main(a: list[str]) -> int:
    if a == ["daemon"]:
        return daemon()
    if a == ["status"]:
        return status()
    if a and a[0] == "report":
        return report(float(a[a.index("--hours") + 1]) if "--hours" in a else 48)
    if len(a) == 4 and a[0] == "eval":          # the daemon's worker process
        r = evaluate(a[1], a[2], a[3])
        print("PHASE " + str(r.get("phase")))
        return 0
    if len(a) == 2 and a[0] == "validate":
        print(json.dumps(validate(a[1]), indent=1)[:4000])
        return 0
    if len(a) >= 3 and a[0] == "build":
        g, item = a[1], a[2]
        head = branch_head(g, item)
        r = evaluate(g, item, head, judge="--no-judge" not in a)
        print(json.dumps({k: x for k, x in r.items() if k not in ("probe",)}, indent=1, ensure_ascii=False)[:5000])
        return 0 if r.get("ok") else 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
