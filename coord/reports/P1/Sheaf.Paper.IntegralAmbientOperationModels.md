## What changed

Filled the completed coefficient-map construction by a limit cone after continuous direct image,
the ambient module adjunction and additivity, the two Roos augmentation coordinate formulas, and
preservation of good representatives by total tensor. The coefficient map is constructed from the
finite projections; no inverse image is commuted with an inverse limit. The Roos comparison is
checked on both mapping-cocone coordinates using the explicit cone map, its shift, and the
augmentation lift.

All existing declaration signatures, public imports and non-theorem constructions are unchanged.
New private helpers have complete proofs. The node records the actual limit, adjunction and cone-
coordinate arguments. No other module is adapted. Local elaboration commands are documented in
`coord/changes/P1-integral-ambient-local-elaboration.md`; the file compiled in 29.3 seconds.

## Proved and sorry left

Closed 6 of the original 10 holes, with no holes added:

- `WeilConjectures.IntegralAmbient.coefficientMap_existsUnique`
- `WeilConjectures.IntegralAmbient.push_isRightAdjoint`
- `WeilConjectures.IntegralAmbient.push_additive`
- `WeilConjectures.IntegralAmbient.pullOperationUnit_coordinates`
- `WeilConjectures.IntegralAmbient.tensorOperationUnit_coordinates`
- `WeilConjectures.IntegralAmbient.tensor_good`

The following original holes remain, all attached to `lem-pur-integral-ambient-operation-models`:

- `WeilConjectures.IntegralAmbient.pullTowerModel`
- `WeilConjectures.IntegralAmbient.tensorTowerModel`
- `WeilConjectures.IntegralAmbient.pull_good`
- `WeilConjectures.IntegralAmbient.integralAmbientOperationModels`

No statement was split off. The remaining theorems retain their original statements, source
citations and proof plans.

## No longer needed

Removed these unused private proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.StrictRoosModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.IntegralTensorReductionTowerComparison`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Sheaf.Paper.ResolvingRepresentativeWhiskering`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.CategoryTheory.StrictRoosDerivation`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`

No entire dependency node or module is declared obsolete: the original unfinished pullback,
tensor-tower and derived-assembly statements still need their recorded mathematical dependencies.
The node retains those proof plans. The new adjunction dependency replaces the proposed
handwritten transport-to-small-site argument for `push_isRightAdjoint`.

## Where the brief, the DAG or earlier work was wrong

The stated adjunction already has a proved independent-universe module-pushforward lemma, so
repeating the small-site construction here is unnecessary. The tensor-reduction module contains a
proved finite comparison with the required scalar-1 normalization and a proved quotient-transition
comparison. The attempted assembly into the slice tower still needs efficient transports between
its scalar-extension models; that original theorem remains unproved, and its attempted proof is
not part of the packet. No statement correction, definition repair, or source-library change was
required. The final derived assembly, the tensor tower and the two pullback obligations remain
unproved in this partial delivery.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
