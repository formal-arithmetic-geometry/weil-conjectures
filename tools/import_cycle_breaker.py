#!/usr/bin/env python3
"""Find and break import cycles of the live Lean library (the human, 2026-10-24: a check reports or acts mechanically;
it never refuses).

A cycle appears when a module of the adopted source library (WeilConjectures.*) imports one of our modules (a proof of
an upstream `sorry` written with our lemmas) and an upstream change, or a landing, makes our module depend on that
upstream module in turn. On 2026-10-24 Adic.LowerStar's imports of three Sheaf modules closed a 90-module cycle after
the upstream sync and the global build failed in 356 modules.

For every strongly connected component of the import graph (lean/Sheaf, lean/WeilConjectures, lean/Comparator):
  - the upstream modules inside it that import our modules inside it are the candidates; the first one whose
    imports of our modules, left out, leave the component acyclic (else all of them) is put back to upstream's text
    at the synced tip (coord/upstream-base.txt, ~/upstream-sync/up), when that text imports no Sheaf module and
    declares every name our version declares; our version and a note go to coord/preferred-upstream/<module>.{lean,md}
    (the worker of the module reads them); one commit and one landing record (group L);
  - otherwise (a cycle of our modules only, or no usable upstream text) it is reported: local/import-cycles.txt and
    the log, for the maintainer and the next red build's handling.

    python3 tools/import_cycle_breaker.py [--dry-run]
Log: ~/cc1/import-cycle-breaker.log (cron, every 5 minutes, under flock)."""
from __future__ import annotations
import fcntl, os, pathlib, re, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import landing as ld  # noqa: E402
import mergelock  # noqa: E402

L = ROOT / "lean"
UP = pathlib.Path.home() / "upstream-sync" / "up"
IMP = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*"
                  r"(?:theorem|lemma|def|instance|abbrev|structure|class)\s+([^\s:({\[]+)", re.M)
LOG = pathlib.Path.home() / "cc1" / "import-cycle-breaker.log"


def log(*a):
    with open(LOG, "a") as f:
        f.write(time.strftime("%F %T ") + " ".join(map(str, a)) + "\n")


def strip(t):
    return re.sub(r"--[^\n]*|/-.*?-/", "", t, flags=re.S)


def graph():
    files = {}
    for top in ("Sheaf", "WeilConjectures", "Comparator"):
        for f in (L / top).rglob("*.lean"):
            if ".lake" not in f.parts:
                files[str(f.relative_to(L))[:-5].replace("/", ".")] = f
    return files, {m: [d for d in IMP.findall(strip(f.read_text(errors="ignore"))) if d in files] for m, f in files.items()}


def sccs(g):
    sys.setrecursionlimit(1000000)
    idx, low, on, st, out, c = {}, {}, set(), [], [], [0]

    def sc(v):
        idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for w in g[v]:
            if w not in idx:
                sc(w); low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v:
                    break
            if len(comp) > 1 or v in g[v]:
                out.append(comp)
    for v in g:
        if v not in idx:
            sc(v)
    return out


def acyclic(g, nodes):
    color = {}
    for s in nodes:
        if s in color:
            continue
        stack = [(s, iter([d for d in g[s] if d in nodes]))]; color[s] = 1
        while stack:
            v, it = stack[-1]
            n = next(it, None)
            if n is None:
                color[v] = 2; stack.pop(); continue
            if color.get(n) == 1:
                return False
            if n not in color:
                color[n] = 1; stack.append((n, iter([d for d in g[n] if d in nodes])))
    return True


def upstream_text(mod):
    try:
        tip = (ROOT / "coord" / "upstream-base.txt").read_text().split()[0]
        return subprocess.run(["git", "show", f"{tip}:{mod.replace('.', '/')}.lean"], cwd=UP, capture_output=True,
                              check=True).stdout
    except (OSError, IndexError, subprocess.CalledProcessError):
        return None


def main() -> int:
    dry = "--dry-run" in sys.argv
    files, g = graph()
    comps = sccs(g)
    report = []
    if not comps:
        (ROOT / "local" / "import-cycles.txt").write_text("")
        return 0
    for comp in comps:
        cs = set(comp)
        cand = sorted({m for m in comp if m.startswith("WeilConjectures.")
                       and any(d.startswith("Sheaf.") and d in cs for d in g[m])})
        chosen = None
        for m in cand:
            g2 = dict(g); g2[m] = [d for d in g[m] if not d.startswith("Sheaf.")]
            if acyclic(g2, cs):
                chosen = [m]; break
        if chosen is None and cand:
            g2 = dict(g)
            for m in cand:
                g2[m] = [d for d in g[m] if not d.startswith("Sheaf.")]
            if acyclic(g2, cs):
                chosen = cand
        usable = []
        for m in chosen or []:
            up = upstream_text(m)
            ours = files[m].read_text(errors="ignore")
            if up is None or re.search(r"^\s*(?:public\s+)?import\s+Sheaf\.", up.decode(errors="ignore"), re.M):
                continue
            if set(DECL.findall(ours)) - set(DECL.findall(up.decode(errors="ignore"))):
                continue
            usable.append((m, up))
        if not usable or len(usable) != len(chosen or []):
            report.append(f"cycle of {len(comp)} modules, not broken mechanically (upstream modules importing ours in it: "
                          f"{', '.join(cand) or 'none'}): {', '.join(sorted(comp)[:20])}")
            continue
        if dry:
            report.append(f"would put back to upstream text: {', '.join(m for m, _ in usable)} (cycle of {len(comp)})")
            continue
        pu = ROOT / "coord" / "preferred-upstream"; pu.mkdir(exist_ok=True)
        lf = open(mergelock.LOCK, "a"); mergelock.acquire(lf, mergelock.LOCK, 3600)
        try:
            with ld.tree_lock():
                prev, paths = {}, []
                for m, up in usable:
                    rel = m.replace(".", "/") + ".lean"; src = L / rel
                    prev[rel] = src.read_bytes()
                    (pu / f"{m}.lean").write_bytes(prev[rel])
                    (pu / f"{m}.md").write_text(
                        f"# {m}: our proof taken out to break an import cycle ({time.strftime('%F')})\n\n"
                        f"Our version imported our modules ({', '.join(d for d in g[m] if d.startswith('Sheaf.'))}), which "
                        f"(through {len(comp)} modules) import this module again. The module is upstream's text again; our "
                        f"version is in {m}.lean next to this note. Land the proof again without importing modules that "
                        "depend on this one (tools/import_cycle_breaker.py).\n")
                    src.write_bytes(up)
                    paths += [f"lean/{rel}", f"coord/preferred-upstream/{m}.lean", f"coord/preferred-upstream/{m}.md"]
                subprocess.run(["git", "add", "--", *paths], cwd=ROOT, check=True)
                names = ", ".join(m for m, _ in usable)
                subprocess.run(["git", "-c", "user.name=Bin Wu", "-c", "user.email=844524296@qq.com", "commit", "-q", "-m",
                                f"Break an import cycle of {len(comp)} modules: {names} back to upstream text "
                                "(our proof kept in coord/preferred-upstream)\n\nCo-Authored-By: Claude Opus 5.5 "
                                "<noreply@anthropic.com>", "--", *paths], cwd=ROOT, check=True)
                r = ld.new_record("L", prev, f"break import cycle: {names} back to upstream text", kind="interface")
                report.append(f"broken: {names} back to upstream text (cycle of {len(comp)}), landing {r['id']}")
        finally:
            fcntl.flock(lf, fcntl.LOCK_UN); lf.close()
    for line in report:
        log(line); print(line)
    (ROOT / "local" / "import-cycles.txt").write_text("\n".join(report) + "\n")
    return 0


if __name__ == "__main__":
    os.environ.setdefault("SHEAF_LEAD", "L-only")
    sys.exit(main())
