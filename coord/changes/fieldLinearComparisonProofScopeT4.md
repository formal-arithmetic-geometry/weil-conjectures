# Field-linear comparison proof elaboration in T4

## Reason

The unchanged baseline exceeded the single-file limit locally. Profiling the existing
resolution-comparison portion showed repeated expensive inference of the two abelian category
structures. Cache those structures locally once. The full module, including the new reduction,
then compiled in 43.1 seconds, without changing the compiler limit or splitting any delivered
file. A nested proof section temporarily restores scalarSheaf's default semireducibility so the
Hom comparison and its natural isomorphism can see its section objects. This section ends
before scalarCohomologyExtEquiv; the existing local irreducibility and exported attributes are
preserved. No declaration signature, visibility, public import, or existing definition body
changes. No target meaning changes and no target review is reopened. No forced adaptations.

## Old

```lean
variable (f : X ⟶ Spec (CommRingCat.of k))
```

scalarSheaf remains locally irreducible throughout the existing comparison section.

## New

```lean
variable (f : X ⟶ Spec (CommRingCat.of k))
local instance : Abelian (SheafOfModules.{u} X.ringCatSheaf) := inferInstance
local instance : Abelian
    (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k)) := inferInstance
```

The cached instances are definitionally the same Mathlib instances previously synthesized at
each use. Their instance attributes are local to this module. The new proof helpers and the
bijection theorem are enclosed by:

```lean
section
attribute [local semireducible] scalarSheaf
-- New private helpers and the proof of the existing bijection theorem.
end
```

The helpers are proved, private, and occur only in proofs. The existing public definitions
retain their exact source bodies, including the scalarCohomologyExtEquiv structure update.

## Users

All direct importers from both roots are listed below, with their locally recorded holders.
The proof-only imports are hidden from importers, the cached abelian structures are
definitionally unchanged, and the transparency section does not escape. Each user keeps the
same signature, data, global attributes, and instance availability; none requires adaptation.
Every transitive user therefore receives the same interface as well.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupUnitCoefficientIdentities | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalGlobalSectionsTensorAffine | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupUnitComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRectangleSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechTensorExact | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductInjective | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1ProductSpanning | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRightCechCupCycleComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ProductResidueH1Injective | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtZeroGlobalSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupZeroGlobalSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPullbackZeroGlobalSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarStructureCoefficientAdjunct | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitExtClass | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRectangleProjectionSectionsTensor | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupZeroGlobalSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalTensorAffineOpenSections | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | T4 | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComplexes | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproduct | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproductComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechModels | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarAffineSectionsExact | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupDegreeZero | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageFirst | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarInverseImageCompositionCoherence | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPullbackTensorCoefficient | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarTensorGlobalSectionsMorphism | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitClassPullback | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyCoordinates | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackComparison | unclaimed | Same interface and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality | unclaimed | Same interface and data; no adaptation. |

## Status

landed 20261014T020517-L-3813991 2026-10-14 (merge of deliver/T4/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
