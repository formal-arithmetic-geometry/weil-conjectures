# AffineDerivedPullbackTensorTilde local transparency

## Reason

The static preflight treats any changed attribute command as an interface change,
including local attributes. This record documents the local transparency settings
used to keep proof elaboration from unfolding large chosen constructions. They do not
change any declaration's signature, definition, or exported reducibility attribute.
All six public statements of the delivered module remain identical.

## Old

There was no local transparency override for these constants in the item:

```lean
-- These constants use their existing global attributes.
```

## New

```lean
attribute [local irreducible] derivedPullback schemeDerivedTensorMonoidal
  Functor.mapDerivedCategory
```

This command affects only the remainder of this module's namespace. The existing
public definitions in their original modules are unchanged. Proof-only imports and
completely proved private helpers are added; all existing public imports are retained.
There are no forced adaptations and no target statement or meaning changes.

## Users

Source-only `tools/downstream.py` reports 884 transitive importers. Its `--uses`
search for `derivedPullback` and `schemeDerivedTensorMonoidal` gives the following
textual users. For every row, the exported signatures, definitions, and instance
choices remain identical; proof bodies and file-local elaboration settings change.
Other transitive importers have the same absence of any exported change.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SingleComplexAffineBaseChange | Z2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlternatingCechBaseChangeFactorization | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineAlternatingCechPinnedMate | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde | J3 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackPerfect | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackPreservesQCoh | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackSingleCohomology | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | N4 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPrecomposePus | X2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageDerivedModel | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | K3 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDescendMorphisms | G1 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorPullback | T4 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectRestrictionClassesSmall | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectTensorHomDuality | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaLocality | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | R1 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMayerVietoris | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChange | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex | T4 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeCriterion | Z2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction | Z2 | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperQCohData | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCase | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseCore | unclaimed | No exported change; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData | unclaimed | No exported change; no adaptation. |

## Status

landed 20261013T060419-L-583582 2026-10-13 (merge of deliver/J3/Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde)
