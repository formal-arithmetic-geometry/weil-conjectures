# Maintenance handoff: suspension-square comparison (Q01, 2026-10-16)

The repeated stage-2 failures were premature dispatch caused by missing statement
dependency edges. `lem-coef-suspension-square-comparison` and its proof helper
`lem-coef-infinity-finite-poset-kan-extension` both use coherent functor categories,
mapping spaces, and cone universal properties owned by
`def-cbc-enhanced-diagrams-cones`, but listed only `def-weil-pbc-simplicial-set`
in `stmt_deps`. The queue therefore admitted the consumer while its actual
definition was still unsplit and unstated. Workers followed the bottom-up brief
correctly. There was no item Lean file, compile failure, return, or stage-2 landing
to repair. The stage-1 merge `deb354a8b0` (live promotion `6491c67f41`) supplied a
natural-language split, not a Lean interface.

Maintenance appended the owning definition to exactly those two `stmt_deps`
lists, in the authoritative live DAG and the side DAG. Live commit: `5a7329b325`.
No statement, proof, proof dependency, review metadata, or Lean binding changed.
The definition has no dependency path back to either node: its all-dependency
closure has four nodes. Existing changed files have adjacent backups ending
`.maint-Q01-suspension-1792152064.bak`. Both repositories are repaired so that
the live-to-side sync retains the correction.

Validation uses the real queue code with each DAG view. The consumer must be
absent from stage 2 while the definition is unstated; the definition and finite-
poset helper must remain open for stage 1. In-memory simulation of the definition
being split, reviewed and given a Lean binding must resume the consumer even
while its proof-only finite-poset theorem remains unstated. The simulation does
not write a binding or change the repository. The existing launcher handoff
regression suite also checks that historical failure counts never suppress ready
work. Only dependency metadata changes; no Lean compilation is needed.

The active dispatcher source already checks held stage-2 claims against their
current `stmt_deps`. No dispatcher change, process restart, failure-count reset,
claim abandonment, or mathematical work is needed. Any worker already running
may finish normally. Normal bottom-up scheduling resumes the required item
when its definition is actually available. At diagnosis the definition was
claimed by NP for stage 1 and the finite-poset helper by Q33; ownership may change.

The worker route guidance is versioned at
`tools/launcher/route-notes/lem-coef-suspension-square-comparison.md` and installed
at `/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-suspension-square-comparison.md`.
Use the published coherent-definition interface when it lands. Do not duplicate
the existing DAG notion or replace coherent comparisons with arbitrary maps,
predicates, or ordinary homotopy-category limits. The finite-poset theorem is
proof-only for this item and does not need a theorem binding before stage 2.

Completed validation: both real DAG views reject premature stage-2 admission and resume it after an in-memory definition binding. All four node comparisons show only the intended stmt_deps addition. The four existing launcher handoff regressions passed locally and on the server. The queue has been regenerated under the merge lock and excludes the consumer from stage 2 while retaining the definition for stage 1. Side metadata/handoff commit: `9dc45b6d58`.
