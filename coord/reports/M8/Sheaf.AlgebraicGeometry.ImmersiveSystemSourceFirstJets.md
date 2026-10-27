## What changed

Replaced the sorry in `AlgebraicGeometry.immersiveSystem_source_first_jets` by a complete
Lean proof from one geometric intermediate theorem. The original statement and public
imports are unchanged. Added the proof imports
`Sheaf.AlgebraicGeometry.ImmersiveSystemSourceLocalFractions` and
`WeilConjectures.AlgebraicGeometry.ClosedPointResidueField`.

The proof constructs the actual coefficient linear map in the supplied frame and proves
rationality of the residue field directly from local finite type and closedness. A proved
private algebra lemma shows that a normalized linear image plus the maximal-ideal square
is closed under products and inverses of units. Polynomial fractions therefore belong to
this submodule, and multiplication by the normalizing unit yields the original claim.
No object is defined by selecting a witness of an unproved existence theorem: the
intermediate theorem is eliminated only inside the proof of the proposition.

The geometric intermediate is polynomial-fraction generation of the *full local ring*,
for arbitrary fields and arbitrary points. It involves neither first jets nor an arbitrary
vector-space linear system, and needs no finite-type, algebraic-closure or closed-point
hypothesis. Its proof plan uses the existing chart-preimage, chart-ring and stalk-localization
interfaces. The remaining bridge is their compatibility with the tensor-pulled sections and
the coefficient germs in a prescribed frame. It is a genuine geometric part of the original
argument, rather than the original jet-surjectivity claim under a new name.

## Proved and sorry left

Original holes closed: 1 of 1,
`AlgebraicGeometry.immersiveSystem_source_first_jets`
(node `lem-zl-immersive-system-source-first-jets`).

New holes added: 1,
`AlgebraicGeometry.immersiveSystem_source_local_fractions`
(node `lem-zl-immersive-system-source-local-fractions`). Its proof is exactly `by sorry`.
No other sorry remains in the delivered Lean files. This is a decomposition, with net hole
change zero, rather than a completed proof without remaining dependencies.

`linear_image_firstOrder` is private and fully proved. The local-ring rationality,
coefficient linearity and change back from the normalized image are also fully proved.
The server compiled the reduction in 7.9 seconds before the final removal of redundant
Mathlib imports; the final compile and delivery preflight are run on the final sources.

## No longer needed

No library modules or original public imports are withdrawn. The original direct proof
dependencies `def-sc-invertible-module`, `def-weil-closed-immersion`,
`def-weil-pbc-morphism-to-projective-space-by-sections`,
`lem-weil-pbc-invertible-generating-sections-fibre` and
`lem-weil-pbc-projective-space-standard-charts` are now used through the geometric
intermediate and remain needed transitively. They are not claimed as pruned.

The main proof uses the source local-finite-type residue-field API directly, so it does not
add an import of the stronger quasi-compact wrapper `Sheaf.AlgebraicGeometry.ClosedPointField`.
No original import was removed. Direct Mathlib polynomial and residue-field proof imports
used during development were redundant with the two final proof imports and were removed.

## Where the brief, the DAG or earlier work was wrong

No false statement, definition repair or source-library adaptation was found. The original
DAG's first-order calculation and frame change were not a ready Lean interface; they are now
implemented by the private algebra lemma. The existing chart and immersion declarations
alone do not identify the coefficient germs of the specific tensor-pullback presentation.
That geometric identification, followed by the standard affine localization calculation,
is recorded in the remaining intermediate instead of moving jet surjectivity again.

Edge cases checked: empty X or empty U₀ supply no x; an empty coordinate family cannot
generate the nonzero invertible stalk; with one coordinate the normalized chart is a point
and its polynomial variables are redundant. The geometric theorem applies over nonclosed
fields and at nonclosed points because it asserts local fractions, not rational residues.
Nilpotents and singular local rings are allowed: the proved algebra uses only the ideal
product m*m and rationality of the residue field. No smoothness or dimension assumption
was inserted. The fixed unit route is preserved.

## New nodes

`lem-zl-immersive-system-source-local-fractions`, in
`dag/nodes/sec-deligne-laumon-general/`, records the polynomial-fraction presentation in
`Sheaf.AlgebraicGeometry.ImmersiveSystemSourceLocalFractions`. Its source is paragraph 3 of
the current finite-cover Bertini blueprint proof, expanded using Stacks 01NE/01NF,
the projective chart-preimage theorem, and affine-open stalk localization. Search included
LeanSearch, LeanFinder, Loogle, Mathlib grep, the projective source APIs and whole-blueprint
searches for coordinate ratios, first jets and local fractions. No matching existing
statement was found. The original node's proof and proof dependencies now track the
compiled reduction. There are no change records because no statement or definition changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
