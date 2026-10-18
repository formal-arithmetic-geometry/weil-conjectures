# AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_kFlat

## Reason

STATEMENT-DISPUTED: the arbitrary ordinary monoidal structure `m` affects the left
side's derived tensorator, but `residueExchangeTensorModelMap` fixes the canonical
ordinary monoidal structure on the right. For a canonical strong monoidal functor
in an additive category, replacing both its lax tensorator and unit by their
negatives is again a strong monoidal structure; its oplax tensorator is negated.
The defining derived tensor/counit square is linear in this comparison. Thus the
left side is negated while the model map is fixed. At odd residue characteristic,
identity pullback on a nonempty geometric point and the degree-zero unit complex
have nonzero residue reduction, so these maps cannot agree for both structures.
The unit complex is K-flat, so the added K-flat hypothesis does not repair this.

The parent needs only the canonical structure. Its original theorem is now proved
directly for every homotopy complex, using the tensor/counit square and braiding.
No target statement or canonical theorem signature changes. The removed nodes
are below the blueprint unit; no realized unit statement or proof step is bypassed.

## Old

```lean
theorem integralResidue_tensorRoute_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))
    (hP : ((f)^*⟦integralCoeff ℓ E⟧).kFlatMap P) :
    letI := residueExchangePullMonoidal ℓ E f m hFlat
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  sorry

theorem integralResidue_tensorRoute_model_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f m hFlat
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  apply integralResidue_tensorRoute_descend ℓ E f m hFlat
  intro P hP
  exact integralResidue_tensorRoute_kFlat ℓ E f m hFlat P hP
```

## New

Both displayed arbitrary-monoidal declarations are withdrawn. The assigned module
is listed in `deleted.txt`; the parent no longer imports it or the descent module.
`integralResidue_tensorRoute_model` keeps its exact statement and is proved from
`Functor.tensorModelRoute_fac`, `Functor.residueDerivedMonoidal_counit`,
`residueOrdinaryUpperStar_braiding`, and the canonical presentation data.
No replacement assertion quantifies over arbitrary monoidal structures.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralResidueTensorRouteKFlat | C2 | Withdrawn; its false arbitrary-monoidal claim has no remaining importer. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | unclaimed | Canonical statement retained; direct normalization proof; arbitrary-m transport removed. |

## Status

landed 20261018T005637-L-2576920 2026-10-18 (merge of deliver/C2/Sheaf.Paper.IntegralResidueTensorRouteKFlat)
