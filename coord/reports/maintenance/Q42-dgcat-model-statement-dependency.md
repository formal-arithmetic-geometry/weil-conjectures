# Q42 maintenance: dg-category model statement prerequisite

The stage-2 retries were caused by an omitted statement dependency, not a Lean
compiler failure. The item explicitly asserts projective cofibrancy of its Hom
complexes, but `lem-coef-projective-cochain-monoidal-model` appeared only in
`proof_deps`. `stmt_deps` contained only `def-weil-size-convention`, a recorded
convention. The bottom-up queue therefore offered the item before the projective
model had a Lean interface. All repeated workers correctly reported that missing
existing DAG prerequisite under the current bottom-up brief.

The Q66 delivery recorded at 2026-10-16T14:41:53Z is a reviewed stage-1 split,
and the Q65 projective-model delivery at 2026-10-16T15:00:47Z is also a stage-1
split. Neither is a Lean statement landing. The live/shared/side records agreed;
this was not a stale clone, missing import, permission problem, or lost artifact.
The sandbox's earlier draft was explicitly rejected and removed: its
proposition-valued placeholders did not encode the laws. Do not restore it.

The repair adds the existing projective-model node to the consumer's `stmt_deps`
and inserts its explicit citation at the projective-cofibrancy clause. This only
makes the existing mathematical dependency explicit. No hypothesis, conclusion,
proof step, proof dependency, Lean binding, or reviewed split is changed.

The authoritative repair belongs in
`~/weil-conjectures-sheaf/dag/nodes/sec-six-functors/lem-coef-dgcat-model-structure.json`
and is mirrored in the same relative path in `~/weil-newtargets`. Side-only DAG
repairs would be overwritten by `sync_newtargets.py`. Both commits are made
under their own repository's `coord/.merge.lock` with `SHEAF_LEAD=L-only` and
the requested Bin Wu identity. Original changed files have the suffix
`.maint-Q42-dgcat-1792170040.bak`. Queue/index outputs are regenerated in the side
project after backing them up; existing unrelated edits are not included in the
maintenance commits.

Validation reproduces the original erroneous stage-2 eligibility, checks the
corrected edge and unchanged fields, confirms there is no dependency path back
from the prerequisite to the item, and verifies automatic eligibility returns
when the prerequisite is marked stated in memory. No Lean source is changed,
so there is no Lean file to compile. No global build is used.

The next worker must use the published projective-model declaration when it
lands. Until then the item genuinely awaits its statement dependency; this is
normal bottom-up readiness, unrelated to the accumulated failure count. Do not
state the prerequisite in this delivery, invent a Mathlib match, restore the
discarded draft, or use `CochainComplex.IsKProjective` alone as the full monoidal
projective-model interface. The project's existing queue and the dispatcher's
held-claim `stmt_deps` check read the corrected edge and will allow the item again
after the prerequisite is stated.

At diagnosis the prerequisite was split/reviewed but unstated. It awaited
`lem-coef-combinatorial-localization-presentability`, which awaited
`def-coef-complete-algebroid`; the latter had genuine unsplit statement inputs.
Those nodes continue through their own normal stage-1/stage-2 tasks. There was
no ready stage-2 frontier to substitute for their required work.
