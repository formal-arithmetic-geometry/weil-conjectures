# WeilConjectures.PrimitiveCounit.finiteTensorBridge

## Reason

Restore the quarantined item and repair its recorded build failure at line 732.
The shared reduction construction now defines unrestrictedIntegralReductionFunctor
as scalarReductionExtension directly. After unfolding the former functor, the
old proof attempts to unfold unrestrictedIntegralReductionExistence, which no
longer occurs. Unfold only the functor being identified and use reflexivity.

The equality proof is proposition-valued; proof irrelevance keeps the transported
isomorphism definitionally equal to the old intended identity isomorphism. The
bridge's signature, functors, tensor map, restrictions and all public imports stay
identical. No target meaning changes, no new data are chosen, and no theorem hole
is moved. Independent review should check this definitional equality.

## Old

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    have h : unrestrictedIntegralReductionFunctor l E W n =
        scalarReductionExtension l E W n := by
      unfold unrestrictedIntegralReductionFunctor scalarReductionExtension
        unrestrictedIntegralReductionExistence scalarReductionExistence
      rfl
    let e := NatIso.mapHomologicalComplex (eqToIso h) (.up ℤ)
    exact ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).mapIso
          ((e.app P).symm.prod (e.app Q).symm))
```

## New

```lean
def finiteTensorBridge (W : Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (scalarReductionSource l E W) ℤ) :
    ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n) :=
  by
    change ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).obj
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj P,
          ((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj
        ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W n)).obj
          (((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
            (.up ℤ)).obj P,
            ((unrestrictedIntegralReductionFunctor l E W n).mapHomologicalComplex
              (.up ℤ)).obj Q))
    have h : unrestrictedIntegralReductionFunctor l E W n =
        scalarReductionExtension l E W n := by
      unfold unrestrictedIntegralReductionFunctor
      rfl
    let e := NatIso.mapHomologicalComplex (eqToIso h) (.up ℤ)
    exact ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).mapIso
      ((coefficientTotalTensor.{u, t+1, t} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n)).mapIso
          ((e.app P).symm.prod (e.app Q).symm))
```

## Users

The source scan of lean/ and quarantine/ finds finiteTensorBridge only in the
item, in TensorModel's normalization equation and its local irreducibility list.
There are no current direct importers under lean/. Quarantined parent modules
and their dependencies remain preserved; none is withdrawn. Since only a proof
of the same functor equality changes, the exported bridge and every predicate
using it remain definitionally equal. No consumer interface changes or forced
adaptations are required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedPrimitiveCounitComparison | C4 | Restore and repair equality proof in finiteTensorBridge; unchanged data and signatures. |

## Status

landed 20261026T114133-L-2268116 2026-10-26 (merge of deliver/C4/Sheaf.Paper.CompletedPrimitiveCounitComparison)
