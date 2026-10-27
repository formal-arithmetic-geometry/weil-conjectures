## What changed

Proved the thirteen theorem holes in `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`
without changing any public signature or definition. The proof builds the two integral
full-subcategory lifts, transports their natural isomorphism through scalar localization,
and localizes the integral identity and pasting equations. Generator independence follows
from the tuple-independent normalization and uniqueness of the completed open exchange.
The DAG proof and proof dependencies now describe this route.

Private proved helpers establish global invertibility from stalkwise invertibility,
residue characteristic, constructible landing, scalar compatibility of the ordinary
reduction tower and its universal derived functor, linearity of completed pullback,
open extension and direct image, and generator independence through a generic
normalization-uniqueness restriction lemma. A generic proved helper transports a
natural isomorphism through scalar localization and records its component formula. Existing private coefficient
and open-extension comparisons are reused from the uniform-restriction module.

## Proved and sorry left

Holes closed (13): `cbcDerivedOpenShriek_additive`, `completedPull_additive`,
`cbcCompactSupportSource_additive`, `cbcCompactSupportTarget_additive`,
`cbcCompactSupportSourceLift_additive`, `cbcCompactSupportTargetLift_additive`,
`cbcCompactSupportSourceLift_linear`, `cbcCompactSupportTargetLift_linear`,
`finiteExtension_compactSupportBaseChange`, `finiteExtension_cbcComplete`,
`finiteExtension_compactSupportBaseChange_identity`,
`finiteExtension_compactSupportBaseChange_horizontal`, and
`finiteExtension_compactSupportBaseChange_vertical`.

Holes added: zero. Holes left in the delivery: zero. Imported theorems retain their
existing proof status; this delivery proves the assigned module from those declarations.
All thirteen declarations realize `thm-cbc-finite-extension`.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.PreservationConstructible`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`
- `Sheaf.Paper.PbcUniformCompleteTriangulated`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.CompletedPullbackTriangles`
- `Sheaf.Paper.FiniteExtensionReductionConeBound`
- `Sheaf.Paper.SbcCompletedOperations`

This proof no longer uses `lem-pod-separated-finite-type-base-change`: separatedness
and local finite type follow from the compactification itself. It replaces
`prop-weil-pbc-preservation-constructible` by
`lem-weil-pbc-actual-coefficient-constructible-preservation`; the latter directly
preserves the chosen completed integral category and requires no additional reduction
interval. Thus `lem-weil-pbc-integral-stratified-perfect-characterization` and
`lem-cbc-finite-extension-reduction-cone-bound` are unnecessary here.

The statement asks for additive and linear scalar transports and natural isomorphisms,
so `lem-cbc-completed-pullback-triangles` is unnecessary for this proof.
`lem-sbc-completed-operations-linear-natural-exchange` is replaced by proved scalar
compatibility through the ordinary module adjunctions and the universal reduction-tower
counit. These are local dependency removals; no module or upstream declaration is
withdrawn. The obsolete corresponding `tool_uses` entries were removed in their
original order. The uniform-complete triangulation node remains used for strict
isomorphism closure via `UniformCompleteTriangulated`.

## Where the brief, the DAG or earlier work was wrong

The original route requested a separate common reduction interval before applying
preservation. The actual-coefficient preservation declaration already gives the needed
conclusion directly. The stated component formula is quantified over every generating
tuple, whereas the rational natural isomorphism is constructed using one finite tuple;
the proof therefore explicitly checks generator independence by unit-normalized
uniqueness. No public statement or definition was changed, no unit route was bypassed,
and no new nodes were introduced.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
