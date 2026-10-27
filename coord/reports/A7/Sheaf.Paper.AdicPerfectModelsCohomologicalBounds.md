## What changed

Replaced the sorry in `Sheaf.Paper.AdicPerfectModelsCohomologicalBounds` by a
complete Lean combination of two bounds, preserving the theorem signature and
all existing definitions and public imports. Both globalization arguments use
finite subcovers on the Noetherian strata, the explicit common interval
`[-sum |a_j|, sum |b_j|]`, exact local restriction, and detection of zero sheaves.
The bound for K is proved without a new obligation: zero coefficient terms remain
zero under the additive completed realization. The residue argument uses one
new single-chart residue calculation, in
`Sheaf.Paper.AdicPerfectModelLocalResidueBounds`.

Private helpers identify identity-coefficient derived pullback with exact module
inverse image, compare the localization representatives, transport homology, and
apply slice-cover separation. Proof imports are private. `import all` exposes
already-proved private helpers for finite-cover extraction, slice separation,
immersion detection and the scalar-extension adjunction; no upstream declaration
was changed. Updated the original node's proof route and added the matching node
for the local calculation. No definition or statement repair, consumer adaptation,
or change record is needed.

## Proved and sorry left

Original holes: 1. Closed original hole:
`AlgebraicGeometry.Scheme.adicPerfectModels_cohomologicalBounds`, node
`lem-sfb-adic-perfect-models-cohomological-bounds`. No sorry remains in the item
module. Its first component, implemented by private `perfectModels_bounds`, is
proved using existing declarations. Its second component, `residueModels_bounds`,
proves the finite-cover and finite-stratum globalization from the local lemma.

Added holes: 1, exactly the public theorem
`AlgebraicGeometry.Scheme.adicPerfectModel_localResidueBounds`, node
`lem-sfb-adic-perfect-model-local-residue-bounds`, in the new module. Its proof is
exactly `by sorry`; its docstring gives the complete mathematical argument.
There are no other added holes and no holes inside definitions.

This is a decomposition, with one original hole closed and one strictly narrower
hole added, not a net hole-count improvement. The remaining statement concerns a
single immersion and slice, a fixed model and fixed interval. It asserts only
local residue vanishing: it has neither stratification nor a cover nor either
global existential bound, and does not repackage the original theorem. The
completed-model bound and the globalization have been removed from its work.

Both files compiled together through lcompile.py; the final check after removing
unused exploratory imports is recorded by the delivery compile/preflight. Edge
cases checked in the argument include empty schemes/stratifications/covers, the
zero model, a>b, I=0 in a field, and infinite residue fields. The sum interval is
ordered even when the index family is empty. Local tensor calculation uses finite
projectivity, not finiteness of the underlying residue set, regularity of A, or
projectivity of A/I over A.

## No longer needed

The original module had only the public data import; it is retained. During
proof development removed unused exploratory imports
`Sheaf.AlgebraicGeometry.NoetherianStratumDetection`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` and
`Mathlib.Data.Finset.Max`.

The revised direct proof no longer needs:

- `lem-sfb-stratified-local-cohomological-bounds`, module
  `Sheaf.AlgebraicGeometry.StratifiedLocalCohomologicalBounds`: finite subcovers,
  explicit sums, exact cohomology transport and zero detection are written here.
- `lem-weil-pbc-proetale-immersion-limit-preservation`, module
  `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`: the proof keeps
  the actual inverse-image completed ring, as the specified local model
  isomorphism already does; no replacement by the completion on the stratum.
- `lem-weil-proetale-weakly-etale-localization`, module
  `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`: restriction to the
  abstract slice U suffices; no comparison to the small site of its scheme.

`lem-sfb-adic-perfect-model-complete-reduction` is no longer a direct import or
dependency of the item, but remains a dependency of the new local residue node.
The other removed direct dependencies may still serve other library consumers;
no module is withdrawn and no whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement found and no target statement changed. The planned
stratified-bounds theorem was stronger than needed for this direct argument.
The existing perfect-model residue calculation lives on a coefficient-sized
small site and does not directly state compatibility with the item's actual
immersion inverse image and localization representatives. The remaining local
lemma records precisely the local tensor/restriction calculation still needed,
rather than assuming that transport silently. The unit's reverse perfect-model
route is retained.

## New nodes

`lem-sfb-adic-perfect-model-local-residue-bounds`, in
`dag/nodes/sec-six-functors-basics/`, realizes the single-chart residue step of
Bhatt--Scholze Proposition 6.6.11. Its module is
`Sheaf.Paper.AdicPerfectModelLocalResidueBounds`. The node records the exact Lean
signature, source, a three-step proof using existing generic comparison/K-flat
lemmas, and LeanSearch, Loogle and Mathlib source searches. It is a strictly local
piece of the original residue argument. No change records were created.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
