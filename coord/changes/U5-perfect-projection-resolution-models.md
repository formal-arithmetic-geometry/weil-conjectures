# AlgebraicGeometry.Scheme.PerfectProjection.Resolution.sourceModel and targetModel

## Reason

Reuse the existing native signed-resolution comparison constructors. The source
comparison is the same composite, with proof arguments identified by proof
irrelevance. The target comparison first removes the quotient pullback isomorphism,
then uses the existing signed comparison. Functoriality of tensor and direct image
identifies this with the old composite: the adjacent quotient isomorphism and its
inverse cancel. No model, differential, representative or scalar action is changed.
This avoids unfolding both large model constructions during each proof conversion.
The normalization theorem's module is a public import because these public
constructions use its public definitions. The comparisons are real constructions
from fully proved theorems; they use no new existence witness.

## Old

```lean
def Resolution.sourceModel :
    aY.tensor.obj ((directImage d f).obj K, quotient d Y n) ≅
      DerivedCategory.Q.obj
        (CochainComplex.mapBifunctor
          (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj r.injective)
          r.coefficient (proEtaleOrdinaryTensor Y (ring d Y))) :=
  aY.tensor.mapIso (Iso.prod (r.pushModel d f K) r.representsQuotient.symm) ≪≫
    mixed Y (ring d Y) aY _ r.coefficient (r.flat d f K).1

def Resolution.targetModel :
    (directImage d f).obj (reduction d aX K n) ≅ DerivedCategory.Q.obj
      (((ordinaryPush d f).mapHomologicalComplex (.up ℤ)).obj (r.targetComplex d f K)) :=
  letI := r.targetComplex_isKInjective d f K
  (directImage d f).mapIso
    (aX.tensor.mapIso (Iso.prod r.representsK
      ((quotientDerivedPullback d f n).symm ≪≫
        (pullback d f).mapIso r.representsQuotient.symm ≪≫
          (proEtaleRingDerivedPullbackFactors f (ring d Y) (ring d X)
            (coefficients d f)).app r.coefficient)) ≪≫
      mixed X (ring d X) aX _ _ (r.flat d f K).2) ≪≫
    (@asIso _ _ _ _ ((ordinaryPush d f).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj (r.targetComplex d f K)))
      (proEtaleRingDerivedDirectImage_kInjective f (ring d Y) (ring d X)
        (coefficients d f) (r.targetComplex d f K))).symm
```

## New

```lean
def Resolution.sourceModel :=
  SignedProjectionResolution.sourceModel f (ring d Y) (ring d X) (coefficients d f)
    aY K (quotient d Y n) r.injective r.isKInjective r.representsK
    r.coefficient r.representsQuotient r.package r.bounded

def Resolution.targetModel :=
  ((directImage d f).mapIso
    (aX.tensor.mapIso (Iso.prod (Iso.refl K) (quotientDerivedPullback d f n)))).symm ≪≫
      SignedProjectionResolution.targetModel f (ring d Y) (ring d X) (coefficients d f)
        aX K (quotient d Y n) r.injective r.isKInjective r.representsK
        r.coefficient r.representsQuotient r.package r.bounded
```

## Users

Both downstream `--uses Resolution.sourceModel` and `--uses Resolution.targetModel`
searches list the item and `ClosedTestScalarModelDiagrams`. The latter's sourceModel
and targetModel are distinct definitions in its own namespace, for condensed test
fibres; it does not refer to this module's Resolution namespace. All hits were read.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PerfectProjectionFormula | U5 | Identical normalized comparisons; totalization_compatibility uses the existing normalization theorem. |
| Sheaf.Paper.ClosedTestScalarModelDiagrams | unclaimed | Unrelated declarations with the same short names; no adaptation. |

No target statement changes meaning. Every retained declaration has the same source,
target and mathematical value. No forced adaptation is needed.

## Status

landed 20261024T191427-L-349376 2026-10-24 (merge of deliver/U5/Sheaf.Paper.PerfectProjectionFormula)
