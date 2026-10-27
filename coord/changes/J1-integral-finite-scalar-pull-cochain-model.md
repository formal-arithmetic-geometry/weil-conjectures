# WeilConjectures.IntegralSystemRealization.integralFiniteScalarPull

## Reason

Move the existing construction, with its signature, body, name and irreducibility unchanged,
from `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare` into the new
`Sheaf.SixFunctors.IntegralFiniteScalarPullCochainModel`. The original module publicly
imports the new module, preserving access for all existing consumers. This avoids an import
cycle between the scalar cochain normalization and the theorem that uses it. The additional
ordinary comparison definitions are actual adjunction constructions; their transpose and
section normalization API is proved. The blueprint attachment moves with the construction,
and the original node records the new owner as a statement dependency. No target statement or coefficient definition changes.

## Old

Module: `Sheaf.SixFunctors.IntegralReductionPullFiniteSquare`.

```lean
@[irreducible] def integralFiniteScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPull l E f ⋙ scalarReductionDerivedExtension l E X n ≅
      scalarReductionDerivedExtension l E Y n ⋙ finiteDerivedPullback l E n f :=
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let q := PurCompactSupport.scalarPull
    (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f
  Functor.isoWhiskerLeft _ (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫ q ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E Y n) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f))
```

## New

Module: `Sheaf.SixFunctors.IntegralFiniteScalarPullCochainModel`, publicly re-exported by
the original module. The declaration is verbatim:

```lean
@[irreducible] def integralFiniteScalarPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ringedPull l E f ⋙ scalarReductionDerivedExtension l E X n ≅
      scalarReductionDerivedExtension l E Y n ⋙ finiteDerivedPullback l E n f :=
  letI := sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  let q := PurCompactSupport.scalarPull
    (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) f
  Functor.isoWhiskerLeft _ (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫ q ≪≫
    Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E Y n) _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryNatIso (PurCompactSupport.finitePullbackIso l E n f))
```

## Users

The source search `tools/downstream.py Sheaf.SixFunctors.IntegralReductionPullFiniteSquare
--uses WeilConjectures.IntegralSystemRealization.integralFiniteScalarPull` reports the four
modules below. Server claim records were read on 2026-10-28. No consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralReductionPullFiniteSquare | J1 | Same declaration, re-exported; its proof is filled. |
| Sheaf.SixFunctors.IntegralFinitePullbackNormalization | unclaimed | Same name, type, body and attribute available through the same import. |
| Sheaf.SixFunctors.IntegralOpenFiniteEvaluation | unclaimed | Same name, type, body and attribute available through the same import. |
| Sheaf.SixFunctors.IntegralOpenScalarUnitSquare | unclaimed | Same name, type, body and attribute available through the same import. |

The direct importers are IntegralFinitePullbackNormalization and IntegralOpenScalarUnitSquare.
The delivery's related-module checks also cover the indirect consumer mentioning the name.

## Status

landed 20261027T234013-L-4160411 2026-10-27 (merge of deliver/J1/Sheaf.SixFunctors.IntegralReductionPullFiniteSquare)
