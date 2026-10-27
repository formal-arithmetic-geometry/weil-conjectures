## What changed

Proved `CochainComplex.hom_total_triangular_resigning` in
`Sheaf.Algebra.Homology.HomTotalTriangularResigning`. The six existing public definitions,
the theorem signature, and the existing public imports are preserved verbatim. Added the
proof import `Mathlib.Algebra.Category.Grp.Zero` and private, fully proved helpers.

The two comparison maps are explicit constructions: a finite signed sum and signed
coordinate projections. Their two composite identities follow from the total coproduct
universal property and coordinate projections. The inverse comparison commutes with the
differentials by testing one generator and its two possible output coordinates; composing
with the inverse identities gives the forward cochain identity. The remaining clauses use direct vanishing,
integer sign arithmetic, `HomComplex.δ_δ`, `Cocycle.equivHomShift`, `δ_ofHomotopy`, and
`δ_rightUnshift`. The derived isomorphism is `DerivedCategory.Q.mapIso T`.

Updated the existing node's proof and proof origin to describe this implementation.
Remote compilation succeeded without errors or warnings in 11.5 seconds, below the
60-second limit. The delivery tool runs the final preflight and axiom checks.

## Proved and sorry left

Closed the one original hole in `CochainComplex.hom_total_triangular_resigning`
(node `lem-sfb-hom-total-triangular-resigning`). No holes remain and no holes were added.
No statements were split off. All private helpers and both private map constructions
are complete Lean proofs and definitions.

## No longer needed

None. All original imports and declared dependencies remain relevant to the constructions
and statements. No nodes or modules are withdrawn. Mathlib's existing square-zero,
shifted cocycle and homotopy lemmas avoid rebuilding their arguments.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG's elementary finite-diagonal argument needs
explicit dependent type transports in Lean, and it is shorter to verify the inverse
cochain map on total coproduct generators before deriving the forward identity. The unit
route, every hypothesis, the specified coordinate formulas and both homotopy identities
are preserved. No existing module outside the assigned item is changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
