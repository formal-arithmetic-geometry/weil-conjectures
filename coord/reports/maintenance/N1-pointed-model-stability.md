# Pointed-model stage-2 handoff repair, 2026-10-16

The five failures were repeated missing-interface reports, not failed proofs.
The stage-1 split of lem-coef-pointed-model-stability landed at 5c51df0f91;
the finite-shape split landed at bd9d97bf1b. Neither was a Lean statement
landing. The worker was instructed both to build bottom-up and not to state
other DAG nodes, while the unified dispatcher had disabled runtime waits and
restarted every held claim irrespective of repaired statement dependencies.

Both statements use coherent diagrams, mapping spaces and cone universal
properties owned by def-cbc-enhanced-diagrams-cones. Their stmt_deps omitted
that definition. The item instead named only ordinary finite limits/colimits;
the finite-shape theorem named only simplicial sets. A missing proof theorem
is not itself a stage-2 prerequisite. Ordinary limits in a homotopy category
do not supply these coherent notions.

Added def-cbc-enhanced-diagrams-cones to stmt_deps of exactly those two nodes
in the authoritative live DAG (78a4309566) and the side DAG (6b299b554a).
All statements, proofs, proof_deps, Lean bindings and review records were
preserved. The definition has no reverse dependency path to either node, so
the two added edges are acyclic. Backups are alongside each changed node as
<filename>.maint-N1-1792141051.bak. Correcting both DAGs prevents side sync
from overwriting the repair.

The launcher source now rechecks a held stage-2 item's statement dependencies
before relaunch. Four regression tests cover missing definitions, resumption
after a binding lands, independence from proof-only dependencies, and continued
dispatch with 10000 historical failures. No Lean file was changed, and no Lean
build or proof work was needed.

For the next worker: use the published binding of
 def-cbc-enhanced-diagrams-cones when it lands. Its stage-1/2 work is already
owned elsewhere; this repair does not fabricate it. The item remains required
and returns to stage 2 once its actual statement dependencies are grounded.
lem-coef-infinity-finite-shape-generation is a proof-only dependency of the
item, so it need not have a theorem binding before the item is stated.
Import proof dependencies that have landed; retain the plan for stage 3.
If a genuinely new notion is still absent, follow the owning definition-node
workflow; never replace mapping-space universal properties by arbitrary Prop
fields or ordinary homotopy-category limits.

The current dispatcher was left running as required. The worker with PID
2568035 exited naturally at 17:17:10 Asia/Shanghai on 2026-10-16, reporting the
corrected direct definition dependency. The ordinary live-sync pass retired
the stale N1 claim at 17:17:11 (coord/ledger.md: "no longer stage-1-open after
live sync"). Our after-exit release helper then found the claim already absent
and made no claim or delivery-log changes. The N1 state subsequently had no
running item worker, and no replacement was launched. Failure history and
the sandbox were retained. No process from another session was killed.

A route note is installed at
/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-pointed-model-stability.md;
the currently running dispatcher reads it on the next worker launch. Its
versioned source is tools/launcher/route-notes/lem-coef-pointed-model-stability.md.
The dispatcher source guard itself is effective on the next normal process
start; the current case is already governed by the corrected queue and the
retired claim. No restart or kill was used for this deployment.

Validation: all four launcher handoff regression tests passed locally and on
the server. JSON comparison against .bak files verified that the only changes
to the four node files were the intended stmt_deps additions. Actual side-DAG
stage2()/eligible() output and the published queue both excluded the two
statements; graph SCC checks found no cycle containing either. The local
shared checkout sees def-cbc-enhanced-diagrams-cones as the actual blocker.
A broad check_dag invocation also encountered existing unrelated dependency
faults elsewhere; no global clean-DAG claim is made by this repair.
