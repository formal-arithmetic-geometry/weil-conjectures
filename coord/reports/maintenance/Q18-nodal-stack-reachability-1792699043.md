# Q18 nodal curve stack: reachability metadata repair

The stage-2 return for immutable head e783a447bf3c requires unreachable flags
on def-sfb-algebraic-moduli-stack, def-sfb-curve-moduli-groupoids, and
def-sfb-ordinary-geometric-node. The parent has left the dependency closure of
all current/former targets. Its missing flag is inherited baseline data;
adding fresh helpers without flags introduces three new landing findings.
Stage-2 preflight rejects import_flags on new nodes as maintainer-owned, so
the worker cannot satisfy this return by editing its delivery packet.

Maintenance registers the exact worker-authored definitions from that head as
unstated DAG prerequisites (lean: null), with maintainer-owned unreachable
flags, and corrects the same missing flag on the parent. Statements, sources,
searches, provenance and dependencies are preserved. No Lean module, binding,
stage-2 acceptance, or review result is installed by this maintenance commit.

The saved packet now supplies these existing prerequisites as dependency
records. Keep the three original Lean files, all saved Lean records (including
the existing ordinary-node declaration), and the item's added stmt_deps.
Each helper needs lean.note; the report names all three under Dependency modules.
Normal per-file compilation and independent statement review remain required.
This registration neither resolves the stage-1 re-split note nor clears the
stage-2 return or Q18 claim. Historical new-node/BLOCKED notes refer to the old base.

Backups use adjacent .maint-Q18-nodal-stack-1792699043.bak files; new paths
have absence-marker backups. No launcher, provider, delivery, review or landing
tool was edited. General protected-tool follow-up: assign maintainer reachability
metadata through the maintainer path and expose landing's global graph findings
in the dry run, so an unassignable field repair is not returned to a worker.
