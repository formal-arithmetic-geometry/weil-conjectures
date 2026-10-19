# Q23 maintenance: dg-module projective resolution

Repeated stage-2 attempts were caused by an omitted statement prerequisite.
`lem-coef-dg-module-projective-resolution` listed only
`def-weil-size-convention` in `stmt_deps`. Its enhanced-localization clauses
retain derived mapping complexes and coherent composition, so they need the
existing `def-coef-complete-algebroid` notion. The proof already reaches that
definition through `lem-coef-dg-enrichment-rectification`. The definition is
split but has neither a Lean binding nor a Mathlib match. Stage 1 completion
does not mean that its statement has been formalized.

The bottom-up worker brief correctly forbids stating another existing DAG node
in this delivery. The missing edge nevertheless made the queue consider this
consumer ready, and the held-claim recheck could not see the omitted prerequisite.
Consequently retries reproduced the same BLOCKED answer. Failure counters,
permissions, the compiler and the 60-second limit were not the cause.

Maintenance adds only `def-coef-complete-algebroid` to the item's `stmt_deps`,
in the authoritative live DAG and the isolated side project. The edge has no
path back to the item through statement or proof edges. The statement, proof,
proof dependencies, review metadata and Lean binding are preserved. In
particular the rectification theorem remains a proof dependency: no proof-only
theorem is being made a stage-2 prerequisite. Both existing node files have an
adjacent `.maint-Q23-dg-module-1792169537.bak` backup.

Use the refreshed shared node when this item becomes eligible again. The
normal queue and the dispatcher's existing held-claim readiness check now see
the prerequisite. Resume after its actual Lean declaration or exact Mathlib
binding lands. This repair does not introduce an attempt limit, reset failure
counts, mark the item complete or formalize its mathematics. No Lean source
changed, so no compilation or global build is appropriate for this repair.

The earlier sandbox drafts under
`scratchpad/lem-coef-dg-module-projective-resolution/` were invalid evidence,
including both `*.lean.txt` files. Do not restore them: arbitrary `Prop` law
fields, tautological localization claims and the incorrect quasi-isomorphism
criterion did not encode the node. The worker reports documented these defects;
no valid active Lean module or binding was produced. The ordinary synchronization
retired the ineligible claim and the dispatcher cleaned its sandbox after the
last running attempt ended. The preserved worker prompts, semantic audits and
logs remain on the launcher under
`/home/ubuntu/weil-launcher-all/run/Q23/lem-coef-dg-module-projective-resolution.*/`.
Initialize a fresh node copy from the current shared base when the item resumes.

The eventual worker must retain arbitrary unbounded modules, the empty/zero dg
category cases, independent size universes, non-flat mapping complexes and all
coherent-enrichment clauses. Compile each eventual Lean file separately through
the prescribed wrapper (60 seconds), then run the normal delivery dry run.
Maintenance claims neither a compiling statement nor successful delivery.
