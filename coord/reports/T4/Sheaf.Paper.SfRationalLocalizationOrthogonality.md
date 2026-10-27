## What changed

Replaced the proof hole in `WeilConjectures.sfRationalLocalizationTriangleOrthogonality`
with the scalar-localization assembly from `IntegralSupportNormalization.integralSupportFunctorNormalization`.
Private helpers construct the normalized closed adjunction through whole-system reduction,
localize adjunctions and exact functors, transport every specified triangle, and prove
cross-object orthogonality in all integer degrees. Public signatures and definition bodies
are preserved. Chosen-model abstraction and explicit local shifts prevent repeated
unfolding during elaboration; no compile limit is changed. The theorem node records the implemented route.

## Proved and sorry left

Closed: `WeilConjectures.sfRationalLocalizationTriangleOrthogonality`
(node `lem-sf-rational-localization-triangle-orthogonality`), one original hole.
Added: zero holes. Split off: zero. No `sorry` remains in the delivered module.
Existing imported proof dependencies remain their owners' work.

## No longer needed

Removed direct proof imports:

- `Sheaf.SixFunctors.OpenRoosUnitAdjunction`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.SfImmersionCompletedPullbackComparison`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.Paper.OpenFiniteConstructibilityInterval`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Mathlib.CategoryTheory.Functor.Derived.Adjunction`
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated` (retained transitively)
- `Sheaf.Paper.IntegralPullbackCompletedComparison`

The direct dependency `lem-sf-integral-immersion-pullback-normalization` is subsumed by
`lem-sf-integral-support-functor-normalization`, which still needs it. Likewise the listed
lower-level integral lemmas remain transitively needed; no module is withdrawn.
`lem-weil-linear-scalar-localization-triangulated` is used through the already chosen
`sfRationalTriangulationDatum` and its exact Q instance. Exactness of the four
localized operations uses the left fraction calculus of the torsion-cone denominators
and Mathlib `Functor.isTriangulated_of_precomp`.
No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The received theorem docstring describes the earlier eight-step integral construction;
the current DAG already factors that work into integral normalization nodes. The proof
uses that factorization. The closed normalization is constructed from the actual reduction,
system pullback/direct-image and total-limit adjunctions, since the support package's
ordinary closed-unit formula is in a different presentation. Empty schemes, zero/torsion
objects, and negative shifts introduce no extra hypotheses in the construction.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
