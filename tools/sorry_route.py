#!/usr/bin/env python3
"""Sorry route of the open targets (launcher, 2026-10-16), written to local/sorry-route.json: {module: [declarations]}.
For each open batch (coord/batchN-targets.txt without coord/batchN-complete.txt) the target modules are compiled in a
scratch file that imports one target module and walks the constants its declarations use (tools/sorry_route.lean);
the modules of used declarations whose own term has `sorry` are the stage-3 work. tools/tag_batches.py reads it.
Usage: tools/sorry_route.py            (refreshes the file)"""
import json, os, pathlib, re, subprocess, time
R = pathlib.Path(__file__).resolve().parent.parent
SB = R / "lean" / ".sandbox" / "_sheaf"; SB.mkdir(parents=True, exist_ok=True)
LIB = (R / "tools" / "sorry_route.lean").read_text()
body = LIB[LIB.index("open Lean Meta"):]
route = {}; failed = []
for n in (1, 2, 3):
    if (R / f"coord/batch{n}-complete.txt").exists(): continue
    p = R / f"coord/batch{n}-targets.txt"
    if not p.exists(): continue
    for mod in [l.strip() for l in p.read_text().splitlines() if l.strip() and not l.startswith("#")]:
        f = SB / f"SorryRoute_{mod.replace('.', '_')}.lean"
        f.write_text(f"module\nmeta import Lean\nimport {mod}\n{body}\n#eval show MetaM Unit from do\n"
                     f"  let env ← getEnv\n"
                     f"  let mi := env.getModuleIdx? `{mod}\n"
                     f"  let decls := env.constants.map₁.toList.filterMap fun (n, _) => if env.getModuleIdxFor? n == mi && !n.isInternalDetail then some n else none\n"
                     f"  for (d, m) in (← sorryRoute decls) do IO.println s!\"ROUTE {{m}} {{d}}\"\n")
        env = dict(os.environ, SHEAF_FILE_TIMEOUT="900")
        r = subprocess.run(["tools/lean_file.sh", str(f.relative_to(R))], cwd=R, env=env, capture_output=True, text=True, timeout=1200)
        out = r.stdout + r.stderr
        hits = re.findall(r"^ROUTE (\S+) (\S+)$", out, re.M)
        if r.returncode and not hits: failed.append(mod); continue
        for m, d in hits: route.setdefault(m, set()).add(d)
        f.unlink(missing_ok=True)
(R / "local").mkdir(exist_ok=True)
(R / "local" / "sorry-route.json").write_text(json.dumps({"t": time.time(), "failed": failed, "route": {m: sorted(v) for m, v in route.items()}}, indent=1))
print(len(route), "modules on the sorry route;", "failed:", failed)
