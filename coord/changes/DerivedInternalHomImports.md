# DerivedInternalHom imports

## Reason

The implementation uses the source-library functorial K-injective resolution and
SheafOfModules.isGrothendieckAbelian directly. The ringed-site resolution theorem and
its localized-generator clauses are unnecessary. QuasiIsoHomComplexMap is needed only
by proofs. This prunes a redundant dependency without changing any declaration type
or the derivedInternalHom definition. No target meaning changes.

## Old

```lean
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
```

## New

```lean
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap
```

All other imports remain unchanged. The proof-only import follows the public imports.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Algebra.Homology.DerivedHomProjectiveResolution | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Algebra.Homology.RhomGlobalSections | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.CanonicalDerivedTensorHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.DerivedDirectImageInternalHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule | unchanged; no adaptation | Mentions quasiIso_homComplex_map only in the proof docstring; no Lean term uses it. |
| Sheaf.AlgebraicGeometry.FiniteDualityDerivedHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.FiniteLocallyFreeDerivedHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.GlobalDerivedHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.SheafExt | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Paper.AffineProjectiveComplexDerivedHom | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Paper.DerivedInternalHomRestrictOpen | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.Paper.DerivedInternalHomStalkLocalization | unchanged; no adaptation | Uses the unchanged derived Hom API; no removed dependency declaration is referenced. |
| Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherent | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.QCqsSheafRHomAdjunction | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.DualizableEvaluationCriterion | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |
| Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology | not adapted | Uses the unchanged derived Hom API; its existing imports suffice. |

## Status

landed 20261012T095918-L-322426 2026-10-12 (merge of deliver/P2/Sheaf.Algebra.Homology.DerivedInternalHom)
