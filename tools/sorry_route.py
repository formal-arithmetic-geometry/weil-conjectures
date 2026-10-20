#!/usr/bin/env python3
"""Sorry route of the open targets (launcher, 2026-10-16; plain scratch files 2026-10-17), written to
local/sorry-route.json.

For each open batch N (coord/batchN-targets.txt without coord/batchN-complete.txt, every N present) and each target
module listed there, a scratch file is compiled through tools/lean_file.sh that imports that one module and walks the
constants its declarations use, transitively through types and values (tools/sorry_route.lean, `sorryRoute`). The
project declarations (roots Sheaf, WeilConjectures) on that walk whose own term contains `sorryAx` are the stage-3 work
of the batch; a sorry the targets import but do not use is not on the route.

The scratch file is a plain Lean file, not a `module`: a `module` file sees neither the private part nor the
non-exposed bodies of what it imports, so the walk found nothing and printed nothing (sorry-route.json was empty from
2026-10-16 to 2026-10-17 and the batch tags fell back to the import closure). 2026-10-20 (b69): it imports only `Lean`;
importing the target failed for every target from 2026-10-19 17:24 (the twin modules Sheaf.X / WeilConjectures.X of the
upstream sync declare the same names; a plain file loads both). The walk reads the project modules' compiled data
itself (tools/sorry_route.lean, `SorryRoute.run`) and resolves a twin name within the importing module's closure.
`commit` in the output is the commit of the published build the walk read; consumers treat as changed since the
route (changed_since) the modules whose source differs from that commit (git), not those with a newer mtime: the
upstream sync rewrote every file and 4397 modules counted as changed.

Assumed results (the human, 2026-10-17): the Lean declarations a batch assumes (coord/assumed.tsv, tools/assumed.py; batch 5
assumes Poincare duality and the Lefschetz trace formula) are axioms of that batch's walk: not descended into, and their
`sorry`s are not its work. The exclusion is per batch: batch 4 proves Poincare duality, so its route keeps them.

Output: {"t", "ok", "failed": [target modules whose walk failed], "route": {module: [declarations]} (union over the open
batches), "batches": {batchN: {module: [declarations]}}, "targets": {target module: {module: [declarations]}} (walks without assumptions), "assumed": {batchN: [declarations]},
"own": {batchN: {module: [declarations]}}, "own_failed": [...]} (see below).
`ok` is false when any target module failed: consumers must not read a partial route as complete (tools/tag_batches.py
then keeps the import closure for that batch and says so). Exit 1 when a walk failed. Since 2026-10-18 a failed run does
not replace a complete local/sorry-route.json: the partial result goes to local/sorry-route-failed.json and the consumers
keep the last complete route (a walk fails transiently while a global build rewrites the .oleans; at 12:27 that day the
fallback to the import closure rewrote the queue without the items below the route and the dispatcher stopped 300+
workers). Only when no complete route exists is the partial file written as before.
Own route, reporting only (the human, 2026-10-18): batch 4's target uses batch 3's target, so batch 4's route counted
all of batch 3's remaining work again. "own" is a separate walk per open batch N with stops = its assumptions plus every
declaration of the target modules of the OTHER open batches (resolved through `declaring()`): another batch's main
theorems, and what only they need, are not N's work; a sorry N also reaches on a path avoiding them still counts. A
target module that imports none of those modules reuses its ordinary walk. Only tools/batch_report.py (new-targets
project) reads "own"; "route", "batches", "targets" and "assumed" are unchanged and are what tools/queue.py,
tag_batches.py and repair_queue.py read. A failed own walk does not make `ok` false: the batch is left out of "own" and
listed in "own_failed" as "batchN:module".
Usage: tools/sorry_route.py [N ...]      (default: every open batch; the file always describes the batches it lists)
       tools/sorry_route.py --check N [MODULE ...]   print batch N's route (its target modules, or the MODULEs given) with
                                                     its assumptions, without writing local/sorry-route.json"""
import hashlib, json, os, pathlib, re, subprocess, sys, time
R = pathlib.Path(__file__).resolve().parent.parent
SB = R / "lean" / ".sandbox" / "_sheaf"; SB.mkdir(parents=True, exist_ok=True)
LIB = (R / "tools" / "sorry_route.lean").read_text()
body = LIB[LIB.index("namespace SorryRoute"):]
sys.path.insert(0, str(R / "tools"))
import assumed  # noqa: E402


def open_batches():
    ns = sorted(int(m.group(1)) for p in (R / "coord").glob("batch*-targets.txt")
                if (m := re.fullmatch(r"batch(\d+)-targets\.txt", p.name)))
    return [n for n in ns if not (R / f"coord/batch{n}-complete.txt").exists()]


def targets(n):
    p = R / f"coord/batch{n}-targets.txt"
    return [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")]


DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public|unsafe|partial)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b", re.M)
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def declaring(mod, depth=0):
    """The modules whose declarations are the targets of `mod`: `mod` itself, or, for a target module that only
    re-exports (Sheaf.Targets.EtaleSmooth is `public import WeilConjectures...Smooth`), the project modules it imports."""
    p = R / "lean" / (mod.replace(".", "/") + ".lean")
    text = p.read_text(errors="ignore") if p.is_file() else ""
    if DECL.search(text) or depth > 2:
        return [mod]
    out = []
    for i in IMP.findall(text):
        if i.split(".")[0] in ("Sheaf", "WeilConjectures"):
            out += declaring(i, depth + 1)
    return out or [mod]


def walk(mod, stops=(), stop_mods=()):
    """{module: set(declarations)} of the sorried project declarations the declarations of `mod` use, not entering the
    declarations `stops` (a batch's assumptions) nor any declaration of the modules `stop_mods` (own route, 2026-10-18:
    the other batches' target modules; those not imported by `mod` are ignored); None on failure."""
    stops = sorted(stops)
    stop_mods = sorted(set(stop_mods))
    tag = ("_A" + hashlib.sha1("\n".join(stops).encode()).hexdigest()[:8]) if stops else ""
    if stop_mods:
        tag += "_O" + hashlib.sha1("\n".join(stop_mods).encode()).hexdigest()[:8]
    f = SB / f"SorryRoute_{mod.replace('.', '_')}{tag}.lean"
    arr = lambda xs: "#[" + ", ".join(f"{json.dumps(x)}.toName" for x in xs) + "]"  # noqa: E731
    # 2026-10-20 (b69): no `import {mod}` (the twin modules collide in one environment); the walk reads the .oleans
    # of the target's project closure itself. Every constant of a loaded stop module is a stop (not entered, not reported).
    f.write_text(f"import Lean\nopen Lean\n\n{body}\n#eval SorryRoute.run {arr(declaring(mod))} {arr(stops)} {arr(stop_mods)}\n")
    env = dict(os.environ, SHEAF_TOOL_TIMEOUT="900")   # SHEAF_FILE_TIMEOUT is reset to 60 by coord/sheaf.env (b69, 2026-10-20)
    r = subprocess.run(["tools/lean_file.sh", str(f.relative_to(R))], cwd=R, env=env, capture_output=True, text=True,
                       timeout=1200)
    out = r.stdout + r.stderr
    nd = re.search(r"^TARGETDECLS (\d+)$", out, re.M)
    if r.returncode or not nd or int(nd.group(1)) == 0:
        print(f"{mod}: walk failed (rc {r.returncode}): " + out.strip()[-3000:], file=sys.stderr)
        return None
    f.unlink(missing_ok=True)
    res = {}
    for m, d in re.findall(r"^ROUTE (\S+) (\S+)$", out, re.M):
        res.setdefault(m, set()).add(d)
    return res


_COMMITS = {}   # route time -> commit of the build it read (changed_since)


def build_commit():
    """The commit of the published build whose .oleans the walk reads (local/builds/published.json), else HEAD."""
    try:
        c = json.loads((R / "local/builds/published.json").read_text()).get("commit")
        if c: return c
    except (OSError, ValueError):
        pass
    r = subprocess.run(["git", "rev-parse", "HEAD"], cwd=R, capture_output=True, text=True)
    return r.stdout.strip() or None


def load():
    """The route as consumers read it: None when local/sorry-route.json is missing, unreadable or not `ok` (a failed
    walk: the caller keeps the import closure and says so); else {"t", "batches": {batchN: set(modules)}, "route": set}."""
    try:
        d = json.loads((R / "local" / "sorry-route.json").read_text())
    except (OSError, ValueError):
        return None
    if not d.get("ok") or "batches" not in d:
        return None
    _COMMITS[d["t"]] = d.get("commit")
    return {"t": d["t"], "commit": d.get("commit"), "batches": {k: set(v) for k, v in d["batches"].items()}, "route": set(d["route"])}


def changed_since(t, modules):
    """Modules whose source changed after the route was computed: a landing may have added a sorry the route does not
    know yet (a split); consumers keep them until the next refresh (~/cc1/sorry-route-loop.sh after each green build).
    2026-10-20 (b69): "changed" means the source differs (git) from the commit of the build the route read; the file
    mtime is used only for a route without a recorded commit (the upstream sync rewrote every file's mtime)."""
    commit = _COMMITS.get(t)
    if commit is None:
        try:
            d = json.loads((R / "local" / "sorry-route.json").read_text())
            if d.get("t") == t: commit = d.get("commit")
        except (OSError, ValueError):
            pass
    if commit:
        r = subprocess.run(["git", "diff", "--name-only", "--no-renames", commit, "--", "lean"], cwd=R,
                           capture_output=True, text=True)
        u = subprocess.run(["git", "ls-files", "--others", "--exclude-standard", "--", "lean"], cwd=R,
                           capture_output=True, text=True)
        if r.returncode == 0:
            paths = {p[len("lean/"):-len(".lean")].replace("/", ".") for p in (r.stdout + u.stdout).split()
                     if p.startswith("lean/") and p.endswith(".lean")}
            return set(modules) & paths
    out = set()
    for m in modules:
        p = R / "lean" / (m.replace(".", "/") + ".lean")
        try:
            if p.stat().st_mtime > t: out.add(m)
        except OSError:
            pass
    return out


def check(n, mods):
    """--check: batch n's route with its assumptions, printed; nothing written"""
    stops = assumed.decls_for(n)
    print(f"batch{n}: {len(stops)} assumed declarations (coord/assumed.tsv)")
    rc = 0
    for mod in mods or targets(n):
        w = walk(mod, stops)
        if w is None:
            rc = 1; continue
        print(f"{mod}: {sum(len(v) for v in w.values())} sorried declarations in {len(w)} modules")
        for m, ds in sorted(w.items()):
            for d in sorted(ds):
                print(f"  {m}\t{d}")
    return rc


def main():
    if sys.argv[1:2] == ["--check"]:
        return check(int(sys.argv[2]), sys.argv[3:])
    ns = [int(a) for a in sys.argv[1:]] or open_batches()
    commit = build_commit()   # before the walks: a build published meanwhile is newer than what they read
    route, batches, tgt, failed = {}, {}, {}, []
    walks = {}   # (module, assumptions) -> walk; tgt keeps the walks without assumptions
    assumed_by = {}
    for n in ns:
        b = batches.setdefault(f"batch{n}", {})
        stops = frozenset(assumed.decls_for(n))
        if stops:
            assumed_by[f"batch{n}"] = sorted(stops)
        for mod in targets(n):
            if (mod, stops) not in walks:
                w = walk(mod, stops)
                if w is None:
                    failed.append(mod); continue
                walks[(mod, stops)] = w
                if not stops:
                    tgt[mod] = w
            for m, ds in walks[(mod, stops)].items():
                b.setdefault(m, set()).update(ds); route.setdefault(m, set()).update(ds)
    # own route (the human, 2026-10-18; reporting only): stop at the other open batches' target modules
    own, own_failed = {}, []
    allopen = open_batches()
    tmods = {n: {d for t in targets(n) for d in [t] + declaring(t)} for n in allopen}
    imports = None
    for n in ns:
        stops = frozenset(assumed.decls_for(n))
        smods = frozenset(set().union(*[tmods[k] for k in allopen if k != n]) - tmods.get(n, set()))
        o, bad = {}, False
        for mod in targets(n):
            w = None
            if smods:
                if imports is None:
                    try:
                        import leanindex
                        imports = leanindex.scan()[1]
                    except Exception as e:   # no index: walk with the stop modules (Lean ignores those not loaded)
                        print("own route: import index unavailable:", e, file=sys.stderr); imports = {}
                clo, todo = set(), [mod]
                while todo:
                    x = todo.pop()
                    for i in imports.get(x, ()):
                        if i not in clo: clo.add(i); todo.append(i)
                if not imports or mod not in imports or clo & smods:
                    key = (mod, stops, smods)
                    if key not in walks:
                        walks[key] = walk(mod, stops, smods)
                    w = walks[key]
                else:
                    w = walks.get((mod, stops))
            else:
                w = walks.get((mod, stops))
            if w is None:
                bad = True; own_failed.append(f"batch{n}:{mod}"); continue
            for m, ds in w.items():
                o.setdefault(m, set()).update(ds)
        if not bad:
            own[f"batch{n}"] = o
    srt = lambda d: {m: sorted(v) for m, v in sorted(d.items())}  # noqa: E731
    out = {"t": time.time(), "commit": commit, "ok": not failed, "failed": failed, "route": srt(route),
           "batches": {k: srt(v) for k, v in batches.items()}, "targets": {k: srt(v) for k, v in tgt.items()},
           "assumed": assumed_by, "own": {k: srt(v) for k, v in own.items()}, "own_failed": own_failed}
    (R / "local").mkdir(exist_ok=True)
    if failed and load() is not None:   # 2026-10-18: keep the last complete route (see the docstring)
        (R / "local" / "sorry-route-failed.json").write_text(json.dumps(out, indent=1))
        print(f"walks failed ({', '.join(failed)}): local/sorry-route.json keeps the last complete route; "
              "this partial result is in local/sorry-route-failed.json", file=sys.stderr)
    else:
        tmp = R / "local" / ".sorry-route.json"; tmp.write_text(json.dumps(out, indent=1)); tmp.replace(R / "local" / "sorry-route.json")
    for k, v in out["batches"].items():
        print(f"{k}: {sum(len(x) for x in v.values())} sorried declarations in {len(v)} modules")
    for k, v in out["own"].items():
        print(f"{k} own: {sum(len(x) for x in v.values())} sorried declarations in {len(v)} modules")
    print("own walks failed:", own_failed)
    print(len(route), "modules on the sorry route;", "failed:", failed)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
