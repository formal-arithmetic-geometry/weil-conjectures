#!/usr/bin/env python3
"""Set builds: a delivery the review agent judges statement-preserving is DONE when its own modules compile on the
frozen tree (the owner, 2026-10-28: "现在的工作是否完成不看全局编译的结果，而看部分集合编译的结果"; final design 17:00 CST).

The frozen tree is the published library: the sources of the last green global build (local/builds/published.json)
and its compiled files lean/.lake/build/lib/lean. Nothing here ever writes there.

A' = every Lean module the delivery changes or adds. It gets a folder of its own, local/sets/<id>/:
  src/<path>.lean       the set's sources
  new/<path>.olean ...  the compiled NEW modules N (absent from the frozen tree)
  changed/<path>.olean  the compiled CHANGED modules X'
  set.json              the record: id, folder, modules, new modules, head, group, item, base frozen build, judgement,
                        result, compile times, probe
Independence (the owner's rule 3): every changed module X' is compiled against the FROZEN tree only, also where it
imports another changed module of the same set (the old, frozen version is used: the statements are unchanged, so the
interface is the same). Only the new modules N are taken from the set (they have no frozen version, so no name
clash). So the new modules are compiled first, in the order of their imports of each other, and then every changed
module at once, in parallel; each compile is `lean -j1` with LEAN_NUM_THREADS=1, LEAN_PATH = the set's new/ : the new
modules of the other recorded sets (local/sets/_new, see below) : the frozen tree : the packages.
Cross-check (rule 4): a changed module that fails against the frozen tree is compiled once more with the set's other
changed modules in front; if it compiles then, the interface of one of them did change: the result is
`interface-changed`, the reviewer's judgement is flagged wrong (local/sets/judgement-wrong.tsv) and the delivery
takes the statement-changing path.
Pass (rule 5): every module of A' compiles this way, the probe (tools/build.py BATCH_PROBE over the compiled modules)
finds no `sorry` the delivery may not leave and no axiom beyond propext, Classical.choice, Quot.sound. Then, with the
switch `on`: the set is recorded as passed (local/sets/passed/<head>.json -> its folder), the delivery is DONE
(tools/queue_mark.py done), its dependents are released (tools/pending_deps.py counts a passed set like a review pass,
so tools/queue.py releases what its new modules state), and its new modules are visible to every compile through
local/sets/_new/lib/lean (symlinks to the newest passed set of each new module, rebuilt atomically by the daemon;
tools/remote_compile_set.py puts it on LEAN_PATH after the frozen tree). Merging A' into the library and into the
frozen .olean happens later, through the ordinary batch landing and the next global build; the record keeps the
texts' hash so that merge can be matched with it.

Who decides that a delivery keeps its statements: the review agent (rule 1). A delivery read by the cc review service
carries the reviewer's `interface` judgement in its verdict (local/verdicts/3/<head>.json); every other delivery gets a
short judgement session of its own (local/sets/judge/<head>.json, a claude -p on the review pool's tokens). The
mechanical comparison (tools/leanindex.py interface_changes) is shown to the agent as reference only.

Measured 2026-10-28 (Sheaf.Paper.AdicCompletedTensorFiniteScalarSquare, proof changed): the public .olean is
byte-identical after a proof-only change (module system; .olean.server/.olean.private/.ilean differ) and Lake then
takes its importers as up to date even in hash mode: a statement-preserving change costs the global build nothing
downstream.

Switch: the file local/sets/MODE: `off`, `shadow` (judge and set-build the waiting deliveries, record the predictions,
change nothing) or `on`; the environment variable SHEAF_SETBUILD overrides it.

Usage:
  tools/setbuild.py daemon               the loop (~/cc1/setbuild-loop.sh; pid local/sets/daemon.pid)
  tools/setbuild.py status               mode, counts, recent results
  tools/setbuild.py report [--hours H]   predictions against what the global build later did with the same heads
  tools/setbuild.py build <G> <module> [--no-judge]   judge (unless told not to) and set-build one delivery branch now
  tools/setbuild.py build <G> <module> --assume-eligible   only the compiles of the set (a test; nothing recorded)
Settings (environment or coord/sheaf.env): SHEAF_SETBUILD_PAR (4 compiles of one set at once), SHEAF_SETBUILD_SETS (3
sets at once), SHEAF_SETBUILD_JUDGES (4 judgement sessions at once), SHEAF_SETBUILD_JUDGE_TIMEOUT (900 s),
SHEAF_FILE_RUN_LIMIT (300 s: how long one compile may run).
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
    m = os.environ.get("SHEAF_SETBUILD")
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


def judgement(head: str) -> dict | None:
    return reviewer_judgement(head) or (read_json(JUDGE / f"{head}.json") if (JUDGE / f"{head}.json").exists() else None)


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
    no declaration is removed or renamed, no instance, `simp`/`ext`/other attribute, `notation`, `macro`, `variable`/
    `open`/`set_option` at file level, or `public import` of an existing module changes. A changed proof is fine.
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


def run_judge(g: str, item: str, head: str, D_mods: list[dict]) -> dict | None:
    """One judgement session; the answer is stored in local/setbuild/judge/<head>.json."""
    sys.path.insert(0, str(SVC))
    import tokenpool as tp  # noqa: E402
    d = JUDGE / head
    d.mkdir(parents=True, exist_ok=True)
    prompt = JUDGE_PROMPT.format(g=g, item=item, head=head[:12], repo=SVC / "clones" / "live", body=judge_body(D_mods))
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
    v = dict(v, source="judge", head=head, group=g, item=item, seconds=round(time.time() - t0),
             cost=(obj or {}).get("total_cost_usd"), time=time.strftime("%FT%TZ", time.gmtime()))
    write_json(JUDGE / f"{head}.json", v)
    log("judge", g, item, head[:9], "eligible" if eligible(v) else "NOT eligible", f"{v['seconds']} s",
        str(v.get("reasoning", ""))[:160].replace("\n", " "))
    return v




# ---------------------------------------------------------------- the compiles of one set

def lean_opts() -> list[str]:
    """[leanOptions] of the lakefile as -D flags (as tools/remote_compile_set.py)."""
    out, on = [], False
    for l in (LEAN / "lakefile.toml").read_text().split("\n"):
        if l.startswith("[leanOptions]"):
            on = True; continue
        if l.startswith("["):
            on = False
        m = re.match(r"([A-Za-z][\w.]*)\s*=\s*([^#]*)", l) if on else None
        if m:
            out.append(f"-D{m.group(1)}={m.group(2).strip().strip(chr(34))}")
    return out


def packages_path() -> list[str]:
    return sorted(str(x) for x in (LEAN / ".lake" / "packages").glob("*/.lake/build/lib/lean"))


def newlib() -> pathlib.Path:
    """The new modules of every passed set, one directory (symlinks), for LEAN_PATH after the frozen tree."""
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
    LEAN_PATH next to the frozen tree: they are handed to Lean one by one (--setup importArts), the frozen tree and the
    packages stay the LEAN_PATH."""
    out = {}
    for m in modules:
        for d in dirs:
            a = arts_of(d, m)
            if a:
                out[m] = a
                break
    return out


def newlib_modules() -> list[str]:
    """The new modules exposed by the passed sets (local/sets/_new)."""
    top = newlib()
    if not top.is_dir():
        return []
    return sorted(".".join(p.relative_to(top).with_suffix("").parts) for p in top.rglob("*.olean"))


def compile_one(folder: pathlib.Path, module: str, outdir: pathlib.Path | None, arts: dict, name: str | None = None,
                root: str = "src") -> dict:
    """lean -j1 of the set's source of `module` against the frozen tree, with the compiled modules `arts` (importArts)
    in front; writes .olean/.ilean (and the module system's .olean.server/.olean.private, .ir) to `outdir` when given.
    {rc, secs, out, errors}."""
    rel = rel_of(module)
    cmd = ["nice", "-n", "0", LEANBIN, "-j1", *lean_opts(), "-R", str(folder / root)]
    if module.startswith("Sheaf."):
        cmd.append("-DautoImplicit=false")      # the Sheaf library's own option (lakefile)
    if outdir is not None:
        o = outdir / rel[:-len(".lean")]
        o.parent.mkdir(parents=True, exist_ok=True)
        for x in o.parent.glob(o.name + ".*"):
            x.unlink()
        cmd += ["-o", str(o) + ".olean", "-i", str(o) + ".ilean"]
    arts = {m: a for m, a in arts.items() if m != module}
    if arts:
        sf = folder / f"setup-{name or module}.json"
        sf.write_text(json.dumps({"name": module, "isModule": False, "importArts": arts, "dynlibs": [], "plugins": [],
                                  "options": {}}))
        cmd += ["--setup", str(sf)]
    limit = int(setting("SHEAF_FILE_RUN_LIMIT", "300"))
    t0 = time.time()
    try:
        p = subprocess.run(cmd + [str(folder / root / rel)], cwd=folder, capture_output=True, text=True, timeout=limit,
                           env=dict(os.environ, LEAN_PATH=":".join(frozen_path()), LEAN_NUM_THREADS="1"))
        rc, out = p.returncode, p.stdout + p.stderr
    except subprocess.TimeoutExpired as e:
        so = e.stdout.decode(errors="ignore") if isinstance(e.stdout, bytes) else (e.stdout or "")
        rc, out = 124, so + f"\n(stopped after {limit} s)"
    errs = [l for l in out.splitlines() if re.search(r":\d+:\d+: error", l) or l.startswith("error")]
    return {"rc": rc if (rc or not errs) else 1, "secs": round(time.time() - t0, 1), "out": out[-6000:], "errors": errs[:20]}


def frozen_path() -> list[str]:
    return [str(PUBLIB)] + packages_path()


def run_probe(folder: pathlib.Path, mods: list[str], arts: dict) -> tuple[dict, str]:
    """{module: {probed, sorry: [constants], axioms: [(decl, axiom)]}} for the compiled modules of the set (tools/build.py
    BATCH_PROBE). One run over all; a module the common run did not reach (an import collision of the probe file
    outside the module system) is probed alone."""
    from build import BATCH_PROBE   # noqa: E402

    def one(ms, name):
        f = folder / "src" / f"{name}.lean"
        f.write_text("import Lean.Elab.Command\n" + "".join(f"import {m}\n" for m in ms)
                     + BATCH_PROBE % ",\n    ".join("`" + m for m in ms))
        sf = folder / f"setup-{name}.json"
        sf.write_text(json.dumps({"name": name, "isModule": False, "importArts": arts, "dynlibs": [], "plugins": [],
                                  "options": {}}))
        try:
            p = subprocess.run([LEANBIN, "--setup", str(sf), str(f)], cwd=folder, capture_output=True, text=True, timeout=600,
                               env=dict(os.environ, LEAN_PATH=":".join(frozen_path()), LEAN_NUM_THREADS="1"))
            out = p.stdout + p.stderr
        except subprocess.TimeoutExpired:
            out = "(probe stopped after 600 s)"
        f.unlink(missing_ok=True)
        return {m: {"probed": bool(re.search(r"SHEAF-PROBED " + re.escape(m) + r" \d+", out)),
                    "sorry": re.findall(r"SHEAF-SORRY " + re.escape(m) + r" (\S+)", out),
                    "axioms": re.findall(r"SHEAF-AXIOM " + re.escape(m) + r" (\S+) (\S+)", out)} for m in ms}, out
    res, out = one(mods, "SetProbe")
    alone = [m for m in mods if not res[m]["probed"]] if len(mods) > 1 else []
    for m in alone:
        r1, o1 = one([m], "SetProbe_" + m.replace(".", "_"))
        res[m] = r1[m]
        out += "\n" + o1[-1500:]
    return res, out[-4000:]


_GRAPH: dict = {}


def library_graph() -> dict:
    """{module: imports} of the library's Sheaf and WeilConjectures modules (the live sources; kept 10 min)."""
    if _GRAPH.get("t", 0) > time.time() - 600:
        return _GRAPH["g"]
    g = {}
    for top in ("Sheaf", "WeilConjectures"):
        for d, _, fs in os.walk(LEAN / top):
            for x in fs:
                if x.endswith(".lean"):
                    p = os.path.join(d, x)
                    try:
                        g[module_of(os.path.relpath(p, LEAN))] = set(imports_of(open(p, errors="ignore").read()))
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
    # those of the reachable unchanged modules that reach a changed module
    rev = {}
    for x in reach | S:
        for i in g.get(x, ()):
            rev.setdefault(i, set()).add(x)
    up, todo = set(), [c for c in S]
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
                          others: list[str], compiles: dict) -> bool:
    """Compile the intermediates from their frozen sources (the published commit) against the set's changed modules,
    in import order, into <folder>/inter/."""
    for m in inter:
        data = subprocess.run(["git", "show", f"{commit}:lean/{rel_of(m)}"], cwd=ROOT, capture_output=True).stdout
        p = folder / "isrc" / rel_of(m)
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(data)
    for m in inter:
        arts = import_arts([folder / "changed", folder / "inter", folder / "new", newlib()],
                           set(changed) | set(inter) | set(new) | set(others))
        c = compile_one(folder, m, folder / "inter", arts, name=m + "-inter", root="isrc")
        compiles["(intermediate) " + m] = c
        if c["rc"]:
            return False
    return True


def set_id(g: str, item: str, head: str) -> str:
    return f"{g}__{item}__{head[:12]}"


def build_set(g: str, item: str, head: str, texts: dict, allowed: dict) -> dict:
    """Compile the set `texts` {rel under lean/: text} of one delivery on the frozen tree (the rules at the top).
    Returns the result; the folder local/sets/<id>/ keeps the sources, the compiled modules and set.json."""
    t0 = time.time()
    sid = set_id(g, item, head)
    folder = SB / sid
    res = {"id": sid, "folder": str(folder), "group": g, "item": item, "head": head, "sha": texts_sha(texts),
           "time": time.strftime("%FT%TZ", time.gmtime())}
    if any(t is None for t in texts.values()):
        return dict(res, ok=False, phase="not-eligible", why="the delivery deletes a module")
    mods = sorted(module_of(r) for r in texts)
    outside = [m for m in mods if not m.startswith(PROJECT)]
    if outside or not mods:
        return dict(res, ok=False, phase="not-eligible", why=f"files outside the library modules: {' '.join(outside) or '-'}")
    while (ROOT / "local" / "PUBLISHING").exists():
        time.sleep(5)
    pub = published()
    res.update(base=pub.get("commit"), base_time=pub.get("time"))
    if folder.exists():
        safe_rmtree(folder)
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
    others = newlib_modules()
    compiles = {}
    # the new modules first, in the order of their imports of each other; each sees the set's new modules compiled
    # before it and the new modules of the other passed sets, and the frozen tree for everything else
    for m in order_new(texts, new):
        arts = import_arts([folder / "new", newlib()], set(new) | set(others))
        c = compile_one(folder, m, folder / "new", arts)
        compiles[m] = c
        if c["rc"]:
            break
    failed = [m for m, c in compiles.items() if c["rc"]]
    if not failed:
        arts = import_arts([folder / "new", newlib()], set(new) | set(others))
        par = int(setting("SHEAF_SETBUILD_PAR", "4"))
        with cf.ThreadPoolExecutor(max_workers=max(1, par)) as ex:
            for m, c in zip(changed, ex.map(lambda x: compile_one(folder, x, folder / "changed", arts), changed)):
                compiles[m] = c
        failed = [m for m, c in compiles.items() if c["rc"]]
    res["compiles"] = {m: {k: c[k] for k in ("rc", "secs", "errors")} for m, c in compiles.items()}
    res["slow"] = sorted(m for m, c in compiles.items() if c["secs"] > 60)
    (folder / "compile.log").write_text("\n\n".join(f"=== {m} rc {c['rc']} {c['secs']} s\n{c['out']}" for m, c in compiles.items()))
    inter, routed = [], False
    if failed and all(m in changed for m in failed) and len(changed) > 1:
        # the lead's measurement (~/cc1/between.py, 2026-10-28): in 97.8 % of deliveries no unchanged module lies on an
        # import path between two changed modules. When some do and a changed module fails against the frozen tree
        # alone, the owner's rule: up to 10 such intermediates are compiled in the set (from their frozen sources,
        # against the set's changed modules) and the failing modules again against them; more than 10: the delivery
        # takes the interface path. Every case is logged (local/sets/intermediates.tsv).
        inter = intermediates(texts, changed)
        res["intermediates"] = inter
        if inter:
            with open(SB / "intermediates.tsv", "a") as f:
                f.write("\t".join([time.strftime("%FT%TZ", time.gmtime()), g, item, head, str(len(inter)),
                                   ",".join(failed), ",".join(inter[:30])]) + "\n")
        if len(inter) > 10:
            routed = True
            res.update(ok=False, phase="interface-path",
                       why=f"{', '.join(failed[:4])} fail(s) against the frozen tree and {len(inter)} unchanged modules lie "
                           "between changed modules of the set (more than 10): the interface path")
        elif inter:
            ok_i = compile_intermediates(folder, inter, pub.get("commit", ""), changed, new, others, compiles)
            if ok_i:
                arts = import_arts([folder / "changed", folder / "inter", folder / "new", newlib()],
                                   set(changed) | set(inter) | set(new) | set(others))
                again = []
                for m in failed:
                    c = compile_one(folder, m, folder / "changed", arts)
                    compiles[m] = dict(c, with_intermediates=True)
                    if c["rc"]:
                        again.append(m)
                res["with_intermediates"] = sorted(set(failed) - set(again))
                failed = again
                res["compiles"] = {m: {k: c.get(k) for k in ("rc", "secs", "errors", "with_intermediates")} for m, c in compiles.items()}
    if routed:
        pass
    elif failed:
        # rule 4: a changed module that compiles only against the set's primed versions shows an interface change
        cross = []
        for m in failed:
            if m in changed and len(changed) > 1 and not inter:
                c2 = compile_one(folder, m, None, import_arts([folder / "changed", folder / "new", newlib()],
                                                              set(changed) | set(new) | set(others)), name=m + "-cross")
                if c2["rc"] == 0:
                    cross.append(m)
        res["cross_check"] = cross
        if cross:
            res.update(ok=False, phase="interface-changed",
                       why=f"{', '.join(cross)} compile(s) only against the set's changed modules, not against the frozen "
                           "tree: the interface of a changed module did change")
        else:
            base_missing = any(re.search(r"unknown module prefix|object file .* does not exist|bad import", " ".join(compiles[m]["errors"]) + compiles[m]["out"][-2000:])
                               for m in failed)
            res.update(ok=False, phase="base-missing" if base_missing else "compile",
                       why=f"{failed[0]}: " + " | ".join(compiles[failed[0]]["errors"][:4])[:1500])
    else:
        probe, ptail = run_probe(folder, mods, import_arts([folder / "changed", folder / "inter", folder / "new", newlib()],
                                                           set(mods) | set(inter) | set(others)))
        res["probe"] = probe
        notrun = [m for m in mods if not probe[m]["probed"]]
        if notrun:
            res.update(ok=False, phase="probe", why=f"the sorry/axiom probe did not run on {', '.join(notrun)}: {ptail[-800:]}")
        else:
            f = sorry_findings(res, allowed, texts)
            res.update(ok=not f, phase="built" if not f else "probe-findings", findings=f)
    if published().get("time") != pub.get("time"):
        res.update(ok=False, phase="infra", why="the published build changed during the set build; built again")
    res["seconds"] = round(time.time() - t0)
    res["allowed_sorry"] = allowed
    write_json(folder / "set.json", res)
    return res
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
    head = head or git("rev-parse", f"refs/heads/deliver/{g}/{item}").strip()
    if not head:
        return None
    base = git("merge-base", "sheaf-dag", head).strip()
    D = s3.read_delivery(s2.Git(ROOT), head, base, g, item)
    over = fix_overrides(head, D["modules"])
    if over:
        D = s3.read_delivery(s2.Git(ROOT), head, base, g, item, overrides=over)
    texts = {m["file"][len("lean/"):]: m["text"] for m in D["modules"] if m["file"].startswith("lean/")}
    return {"group": g, "item": item, "head": head, "D": D, "texts": texts, "sha": texts_sha(texts), "fixed": sorted(over),
            "roles": sorted({m.get("role") for m in D["modules"]}), "fails": D["fails"]}


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


def evaluate(g: str, item: str, head: str, judge: bool = True) -> dict:
    """Judgement, then the set build when the delivery is judged statement-preserving. The result is stored in
    local/sets/results/<head>.json (and the set's folder); in mode `on` a passing set is recorded as passed."""
    dv = delivery(g, item, head)
    if dv is None:
        return {"head": head, "ok": False, "phase": "gone"}
    texts = dv["texts"]
    sha = texts_sha(texts)
    prev = read_json(RESULTS / f"{head}.json")
    if prev and prev.get("sha") == sha and prev.get("base_time") == published().get("time") \
            and prev.get("phase") not in ("infra", "no-judgement", "wait-reader"):
        return prev
    base = {"head": head, "group": g, "item": item, "sha": sha, "roles": dv["roles"], "fixed": dv["fixed"],
            "base": published_commit(), "base_time": published().get("time"), "time": time.strftime("%FT%TZ", time.gmtime())}

    def done(r):
        write_json(RESULTS / f"{head}.json", r)
        log(g, item, head[:9], r.get("phase"), "PASS" if r.get("ok") else "-", f"{r.get('seconds', 0)} s",
            str(r.get("why") or "; ".join(r.get("findings") or []))[:240].replace("\n", " "))
        return r
    if dv["fails"]:
        return done(dict(base, ok=False, phase="static", why="; ".join(f"({L}) {x}" for L, x in dv["fails"][:4])))
    if set(dv["roles"]) - {"item", "new", "adapted"}:
        return done(dict(base, ok=False, phase="not-eligible", why=f"roles {', '.join(map(str, dv['roles']))}"))
    v = read_json(ROOT / "local" / "verdicts" / "3" / f"{head}.json") or {}
    if v.get("verdict") == "RETURN":
        return done(dict(base, ok=False, phase="returned", why="the reviewer returned this head"))
    j = judgement(head)
    if j is None:
        reader = needs_reader(g, item, dv["D"]) if not v else None
        if reader:
            return dict(base, ok=False, phase="wait-reader", why=reader)   # the reviewer's verdict will carry it
        if not judge:
            return dict(base, ok=False, phase="no-judgement")
        j = run_judge(g, item, head, dv["D"]["modules"])
        if j is None:
            return dict(base, ok=False, phase="no-judgement")
    base["judgement"] = {k: j.get(k) for k in ("statement_unchanged", "downstream_affected", "source", "reasoning",
                                                "new_public_declarations")}
    if not eligible(j):
        return done(dict(base, ok=False, phase="not-eligible", why="judged statement-changing or downstream-affecting"))
    allowed = allowed_sorry(dv["D"]["modules"])
    r = build_set(g, item, head, texts, allowed)
    r = dict(base, **r)
    if r.get("phase") == "interface-changed":
        with open(SB / "judgement-wrong.tsv", "a") as f:
            f.write("\t".join([time.strftime("%FT%TZ", time.gmtime()), g, item, head, str(j.get("source")),
                               ",".join(r.get("cross_check") or [])]) + "\n")
    write_json(pathlib.Path(r["folder"]) / "set.json", r) if r.get("folder") else None
    if r.get("ok") and mode() == "on":
        record_passed(r)
    return done(r)


# ---------------------------------------------------------------- passed sets

def record_passed(r: dict) -> None:
    """The set passed: record it (rule 5), mark the item done, expose its new modules. Idempotent."""
    p = PASSED / f"{r['head']}.json"
    if (read_json(p) or {}).get("sha") == r["sha"]:
        return
    write_json(p, {k: r.get(k) for k in ("id", "folder", "group", "item", "head", "sha", "modules", "new_modules",
                                         "changed_modules", "base", "base_time", "judgement", "time")}
               | {"passed": time.strftime("%FT%TZ", time.gmtime())})
    try:
        subprocess.run([sys.executable, str(ROOT / "tools" / "queue_mark.py"), "done", "3", r["item"],
                        "--note", f"set build {r['id']} passed"], cwd=ROOT, capture_output=True, timeout=120)
    except Exception:  # noqa: BLE001
        pass
    log("PASSED", r["group"], r["item"], r["head"][:9], "set", r["id"], "new modules:", " ".join(r.get("new_modules") or []) or "-")
    refresh_newlib()


def passed_heads() -> dict:
    """{head: record} of the passed sets whose head is still its branch's head (not merged, not replaced)."""
    if mode() != "on" or not PASSED.is_dir():
        return {}
    live = {h for _g, _i, h in candidates()}
    out = {}
    for p in PASSED.glob("*.json"):
        r = read_json(p)
        if r and r.get("head") in live:
            out[r["head"]] = r
    return out


def is_passed(g: str, item: str, head: str) -> bool:
    """tools/pending_deps.py: a passed set counts as a review pass (its dependents are released)."""
    if mode() != "on":
        return False
    r = read_json(PASSED / f"{head}.json")
    return bool(r) and r.get("group") == g and r.get("item") == item


_SOURCES: dict = {}


def passed_sources() -> dict:
    """{module: path of its source in the passed set} for the passed sets whose head is live (switch on); kept 60 s.
    tools/own_decl.py reads a module from here first, so the progress count and the queue see a passed set's module
    as written (done) before its merge into the library."""
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
    """local/sets/_new/lib/lean: symlinks to the compiled new modules of every passed set whose head is live and whose
    module the frozen tree does not have yet; rebuilt beside and switched with one rename of a symlink."""
    SB.mkdir(parents=True, exist_ok=True)
    gen = SB / f"_new.{int(time.time() * 1000)}"
    lib = gen / "lib" / "lean"
    lib.mkdir(parents=True)
    n = 0
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
                n += 1
    tmp = SB / "_new.link.tmp"
    tmp.unlink(missing_ok=True)
    tmp.symlink_to(gen.name)
    old = os.path.realpath(NEWLINK) if NEWLINK.is_symlink() else None
    os.replace(tmp, NEWLINK)
    for d in SB.glob("_new.[0-9]*"):
        if d.resolve() != gen.resolve() and time.time() - d.stat().st_mtime > 600:
            safe_rmtree(d)


# ---------------------------------------------------------------- the daemon

def daemon() -> int:
    SB.mkdir(parents=True, exist_ok=True)
    lockf = open(SB / "daemon.lock", "w")
    try:
        fcntl.flock(lockf, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        print("another daemon runs"); return 1
    (SB / "daemon.pid").write_text(str(os.getpid()))
    log("daemon started, mode", mode())
    width = int(setting("SHEAF_SETBUILD_SETS", "3")) + int(setting("SHEAF_SETBUILD_JUDGES", "4"))
    ex = cf.ThreadPoolExecutor(max_workers=width)
    running, tried = {}, {}
    last_new = 0.0
    while True:
        if mode() == "off":
            time.sleep(30); continue
        for h, fut in list(running.items()):
            if fut.done():
                running.pop(h)
                try:
                    fut.result()
                except Exception as e:  # noqa: BLE001
                    log("evaluate failed", h[:9], repr(e)[:300])
        try:
            cands = candidates()
        except Exception as e:  # noqa: BLE001
            log("candidates failed", repr(e)[:300]); cands = []
        pt = published().get("time")
        for g, item, head in cands:
            if head in running or len(running) >= width:
                continue
            r = read_json(RESULTS / f"{head}.json")
            if r and r.get("ok") and mode() == "on" and r.get("base_time") == pt and r.get("group") == g \
                    and not (PASSED / f"{head}.json").exists():
                try:
                    record_passed(r)          # built in shadow mode, switched on since
                except Exception as e:  # noqa: BLE001
                    log("record_passed failed", head[:9], repr(e)[:200])
            if r and r.get("base_time") == pt and r.get("phase") not in ("infra",):
                continue
            if r and r.get("phase") in ("not-eligible", "static", "returned"):
                continue
            if time.time() - tried.get(head, 0) < 900:
                continue
            tried[head] = time.time()
            running[head] = ex.submit(evaluate, g, item, head)
        if mode() == "on" and time.time() - last_new > 300:
            try:
                refresh_newlib()
            except Exception as e:  # noqa: BLE001
                log("refresh of _new failed", repr(e)[:300])
            last_new = time.time()
        time.sleep(20)


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
        elif pred in ("compile", "interface-changed", "probe-findings"):
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
    print("mode", mode())
    rs = [read_json(p) or {} for p in RESULTS.glob("*.json")] if RESULTS.is_dir() else []
    by = {}
    for r in rs:
        by[r.get("phase")] = by.get(r.get("phase"), 0) + 1
    print("results by phase:", json.dumps(by, sort_keys=True))
    secs = sorted(r.get("seconds") or 0 for r in rs if r.get("phase") in ("built", "compile", "probe-findings"))
    if secs:
        print(f"set build seconds: median {secs[len(secs) // 2]}, max {secs[-1]} ({len(secs)} builds)")
    print("passed sets with a live head:", len(passed_heads()))
    return 0


def main(a: list[str]) -> int:
    if a == ["daemon"]:
        return daemon()
    if a == ["status"]:
        return status()
    if a and a[0] == "report":
        return report(float(a[a.index("--hours") + 1]) if "--hours" in a else 48)
    if len(a) >= 3 and a[0] == "build":
        g, item = a[1], a[2]
        head = git("rev-parse", f"refs/heads/deliver/{g}/{item}").strip()
        if "--assume-eligible" in a:      # a test of the compiles alone: no judgement, nothing recorded as passed
            dv = delivery(g, item, head)
            r = build_set(g, item, head, dv["texts"], allowed_sorry(dv["D"]["modules"]))
        else:
            r = evaluate(g, item, head, judge="--no-judge" not in a)
        print(json.dumps({k: v for k, v in r.items() if k not in ("probe",)}, indent=1, ensure_ascii=False)[:5000])
        return 0 if r.get("ok") else 1
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
