#!/usr/bin/env python3
"""Remove the imports a finished module does not use (the human, 2026-10-16: "每个代码完工后都要检查import到底用没用到，
没用到的记得剪枝").

For a module without sorry: compile a copy with Mathlib's `#min_imports` (lean_file.sh), which prints the smallest set of
modules its declarations need; keep the current imports needed to reach that set (dropping an import whose needed
modules another kept import already reaches), remove the others; then the new file must compile alone and pass
tools/import_prune_check.py (no downstream module relied on a removed import); only then is it written. The global
build verifies the commit.

Usage: tools/prune_imports.py [--commit] <module> ...      prune these modules
       tools/prune_imports.py --loop                       every 20 min: modules proved since the last pass first, then
                                                           the finished modules of the targets' closure (backlog), a few
                                                           per pass; state local/prune-imports.json, log local/prune-imports.log
"""
import json, os, pathlib, re, subprocess, sys, time
R = pathlib.Path(__file__).resolve().parent.parent; sys.path.insert(0, str(R / "tools"))
import leanindex as li
LEAN = R / "lean"; SB = LEAN / ".sandbox" / "_sheaf"; STATE = R / "local" / "prune-imports.json"; LOG = R / "local" / "prune-imports.log"
IMP = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)\s*$")
HOLE = re.compile(r"\b(sorry|admit)\b")


def log(*a):
    with open(LOG, "a") as f: f.write(time.strftime("%F %T ") + " ".join(str(x) for x in a) + "\n")


def strip(t): return re.sub(r"--[^\n]*|/-.*?-/", "", t, flags=re.S)


def path(m): return LEAN / (m.replace(".", "/") + ".lean")


def lean_file(f, timeout_s):
    env = dict(os.environ, SHEAF_FILE_TIMEOUT=str(timeout_s))
    p = subprocess.run(["tools/lean_file.sh", str(f.relative_to(R))], cwd=R, env=env, capture_output=True, text=True, timeout=timeout_s + 120)
    return p.returncode, p.stdout + p.stderr


def closure(m, imports, memo):
    if m in memo: return memo[m]
    seen, st = {m}, [m]
    while st:
        x = st.pop()
        for i in imports.get(x, ()):
            if i not in seen: seen.add(i); st.append(i)
    memo[m] = seen; return seen


def prune(m, imports, memo):
    """(new text or None, reason)."""
    p = path(m); old = p.read_text()
    if HOLE.search(strip(old)): return None, "has sorry"
    lines = old.split("\n"); imp_idx = [k for k, l in enumerate(lines) if IMP.match(l)]
    if len(imp_idx) < 2: return None, "fewer than two imports"
    cur = [IMP.match(lines[k]).group(4) for k in imp_idx]
    SB.mkdir(parents=True, exist_ok=True); t = SB / f"Prune_{m.replace('.', '_')}.lean"
    body = lines[:imp_idx[-1] + 1] + ["import Mathlib.Tactic.MinImports"] + lines[imp_idx[-1] + 1:] + ["", "#min_imports"]
    t.write_text("\n".join(body))
    rc, out = lean_file(t, 240); t.unlink(missing_ok=True)
    if rc: return None, "min_imports run failed: " + out.strip().splitlines()[-1][:150] if out.strip() else "min_imports run failed"
    need = [IMP.match(l.strip()).group(4) for l in out.splitlines() if IMP.match(l.strip())]
    need = [x for x in need if x != "Mathlib.Tactic.MinImports"]
    if not need: return None, "no #min_imports output"
    reach = {i: closure(i, imports, memo) if i in imports else {i} for i in cur}
    covers = {i: {n for n in need if n in reach[i]} for i in cur}
    if any(not any(n in reach[i] for i in cur) for n in need): return None, "a needed module is outside the current imports' closure"
    keep = [i for i in cur if covers[i]]
    for i in sorted(list(keep), key=lambda x: len(covers[x])):       # drop imports whose needs other kept imports cover
        others = set().union(*(covers[j] for j in keep if j != i)) if len(keep) > 1 else set()
        if covers[i] <= others: keep.remove(i)
    drop = [i for i in cur if i not in keep]
    if not drop: return None, "all imports used"
    new = "\n".join(l for k, l in enumerate(lines) if not (k in imp_idx and IMP.match(l).group(4) in drop))
    p.write_text(new)
    try:
        rc, out = lean_file(p, 60)
        if rc: return None, "pruned file does not compile: " + next((l for l in out.splitlines() if "error" in l), "")[-200:]
        o = SB / f"PruneOld_{m.replace('.', '_')}.lean"; o.write_text(old)
        c = subprocess.run([sys.executable, "tools/import_prune_check.py", m, str(o), str(p)], cwd=R, capture_output=True, text=True, timeout=600)
        o.unlink(missing_ok=True)
        if c.returncode: return None, "downstream relies on a removed import: " + c.stdout.strip().replace("\n", " ")[:200]
    finally:
        p.write_text(old)
    return new, "drop " + ", ".join(drop)


def commit(done):
    if not done: return
    for m, new in done.items(): path(m).write_text(new)
    files = [str(path(m).relative_to(R)) for m in done]
    msg = f"Prune unused imports of {len(done)} finished module(s) (tools/prune_imports.py)\n\n" + "\n".join(f"- {m}" for m in done) + "\n\nCo-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
    r = subprocess.run(["flock", "-w", "300", "coord/.merge.lock", "git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m", msg, "--", *files],
                       cwd=R, env=dict(os.environ, SHEAF_LEAD="L-only"), capture_output=True, text=True)
    log("commit", "ok" if r.returncode == 0 else "FAILED " + r.stderr[-200:], len(done))


def run(mods, do_commit):
    _, imports = li.scan(); memo = {}; done = {}
    for m in mods:
        if not path(m).is_file(): continue
        try: new, why = prune(m, imports, memo)
        except Exception as e: new, why = None, repr(e)[:150]
        log(m, "|", why)
        if new: done[m] = new
    if do_commit: commit(done)
    return done


def loop():
    while True:
        try:
            st = json.loads(STATE.read_text()) if STATE.exists() else {}
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=R, capture_output=True, text=True).stdout.strip()
            since = st.get("head")
            recent = []
            if since:
                out = subprocess.run(["git", "log", "--format=", "--name-only", f"{since}..{head}", "--", "lean"], cwd=R, capture_output=True, text=True).stdout
                recent = sorted({".".join(pathlib.Path(f).relative_to("lean").with_suffix("").parts) for f in out.split() if f.endswith(".lean")})
            backlog = st.get("backlog")
            if backlog is None:
                _, imports = li.scan()
                tc = [l.split()[-1] for l in (LEAN / "TargetsCheck.lean").read_text().splitlines() if IMP.match(l)]
                seen, stack = set(), list(tc)
                while stack:
                    x = stack.pop()
                    if x in seen or x not in imports: continue
                    seen.add(x); stack.extend(imports[x])
                backlog = sorted(seen)
            batch = [m for m in recent if path(m).is_file()] + backlog[:40]
            backlog = backlog[40:]
            run(batch, True)
            STATE.write_text(json.dumps({"head": head, "backlog": backlog, "t": time.time()}))
        except Exception as e:
            log("loop error", repr(e)[:300])
        time.sleep(1200)


if __name__ == "__main__":
    a = sys.argv[1:]
    if a[:1] == ["--loop"]: loop()
    else:
        c = "--commit" in a; mods = [x for x in a if not x.startswith("--")]
        d = run(mods, c); print(f"{len(d)} of {len(mods)} module(s) pruned" + ("" if c else " (dry run; --commit writes)")); print(open(LOG).read().splitlines()[-1] if LOG.exists() else "")
