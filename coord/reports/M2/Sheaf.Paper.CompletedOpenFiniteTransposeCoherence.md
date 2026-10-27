## What changed

Filled `AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose.completedOpenFiniteTransposeCoherence`
in `Sheaf.Paper.CompletedOpenFiniteTransposeCoherence`, retaining every existing statement and
comparison definition. Private category lemmas express transport of transposes and units. The
ordinary scalar/open comparison is its defining inverse mate, and exact localization preserves
that equation. Section-normalized conjugate uniqueness identifies the constant and ringed
pullback compositors. The existing scalar-restriction cube then proves the pulled-back unit
identity. Its private calculation keeps the compositor as a parameter, and is applied to the fixed
constantSquare, so the kernel checks naturality without expanding the derived compositors.
An explicit equality of the scalar-restricted objects transports both endpoints before
composing the identities; reflexive endpoint transports then cancel. The two previously
proved naturality/strict clauses are retained.

Added proof imports of `Sheaf.SixFunctors.ExactLocalizationInverseMate` and
`Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction` (only its proved generic
`exact_adjunction_eq` helper), and private access to the existing proved
`exchangeResPull_square` helper of `Sheaf.Paper.StrictTowerExchangeMateNormalization`.
Added `Sheaf.Paper.ConstantTowerSquareNormalization`, a proved public wrapper of the existing
`cbcEvaluationConstantTowerSquare` private helper in `CompleteProetaleStrictTowerRealization`.
Its inverse natural-transformation equality supplies the remaining compositor normalization, without applying the containing
realization theorem. This removes a duplicate ordinary/derived compositor calculation.
The proof uses explicit alias normalization without a file-wide transparency override.
The containing normalization theorem and semilinear evaluation theorem are not applied.
Updated the item's node proof, proof dependencies and proof origin to describe this route.

## Proved and sorry left

Closed the one remaining hole:
`AlgebraicGeometry.Scheme.CompletedOpenFiniteTranspose.completedOpenFiniteTransposeCoherence`
(node `lem-cbc-completed-open-finite-transpose-coherence`).

No holes added and no `sorry` remains in the two delivered modules. The new theorem
`AlgebraicGeometry.Scheme.exchangeConstantTowerSquare_inv` is proved from the existing helper. The existing
`completedOpenFiniteTransposeCoherence_naturality` and
`completedOpenFiniteTransposeCoherence_strict` remain proved. No decomposition.

Validation: the two-file server compile accepted both delivery modules. All 15 existing
declaration signatures and definition bodies were checked against the shared source.
The resulting long-line warning was fixed before submission.

## No longer needed

Removed these direct proof imports and their planned dependency uses:

- `Sheaf.Algebra.Homology.DiagramKFlatReplacements`:
  `lem-weil-pbc-diagram-kflat-replacements`.
- `Sheaf.Algebra.Homology.RingedOpenFlatResolution`:
  `lem-cbc-ringed-open-flat-resolution`.
- `Sheaf.Paper.FlatCommonQuotientReductionTower`:
  `lem-weil-pbc-flat-common-quotient-reduction-tower`.
- `Sheaf.Paper.RingedCommonQuotientPullbackComparison`:
  `lem-weil-pbc-ringed-common-quotient-pullback-comparison`.
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`:
  `lem-pur-cochain-pullback-tensor-coherence`.
- `Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat`:
  `lem-weil-pbc-flat-scalar-restriction-kflat`.
- `Sheaf.Paper.KFlatRingedToposPullback`:
  `lem-weil-pbc-ringed-pullback-preserves-kflat`.
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`:
  `lem-pur-left-derived-from-kflat-class`.
- `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`:
  `lem-sp-exact-derived-transformation-pasting`.

The scalar/open comparison is already defined by its mate, so the main theorem of
`Sheaf.CategoryTheory.RingedOpenScalarAdjunction` (`lem-cbc-ringed-open-scalar-adjunction`)
is not needed here. The statement-side imports/definitions from
`lem-weil-pbc-constant-completion-equivalence`, `lem-sf-open-tensor-normalization`,
`def-weil-extension-by-zero-presheaf`, and `def-weil-presheaf-modules-sheafification`
are retained, but their standalone theorems are not used as proof steps. The historical `tool_uses` record is retained; the revised proof dependencies
record the tools actually used by this proof.
These are local dependency removals; no module is withdrawn, and dependencies used by
other declarations remain available.

## Where the brief, the DAG or earlier work was wrong

The earlier plan repeats flat-resolution, balanced-tensor and quotient-transition work
already packaged in the fixed comparison definitions. Naturality cancels the actual/datum
and quotient/open transports. What remains is the exact localized scalar mate and the
scalar-restriction square, plus identification of the two normalized constant compositors.
The previous G5 report correctly suggested this shorter category-theoretic route.
The statement, its edge cases (zero input, empty or identity open, and degenerate quotient),
and the blueprint unit's open/proper factorization route are unchanged. The proof uses no
nonzero or nonempty assumption and works on whole strict tower derived categories.

## New nodes

`lem-cbc-constant-tower-square-normalization` records the inverse natural-transformation equality of the constant
ringed strict-tower square with the specified compositor. Its new module
`Sheaf.Paper.ConstantTowerSquareNormalization` reuses a complete existing proof; it adds zero
holes. It is strictly the compositor-identification part of the item, with no open unit,
scalar restriction or quotient transport in its statement. Its dependency closure does not
reach the item. No existing definitions or statements change.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
