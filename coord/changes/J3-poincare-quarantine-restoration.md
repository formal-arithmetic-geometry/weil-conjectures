# AlgebraicGeometry.ProEtale.CondensedRing.isIso_poincareMap

## Reason

Restore the quarantined source module and repair its recorded kernel type
mismatch. A proved private helper carries out the isomorphism argument in abstract
monoidal closed categories, avoiding the broad unfolding of concrete
monoidal-closed instances. Every signature, attribute,
public import and non-theorem body is verbatim from the current quarantine
archive. No definition or target statement changes.

## Old

```lean
theorem isIso_poincareMap : IsIso (poincareMap ℓ p d) := by
  have := isIso_verdierExchange ℓ p (𝟙_ _) (𝟙_ _)
  unfold poincareMap Verdier.poincareMap
  exact inferInstanceAs (IsIso (_ ≫ verdierExchange ℓ p (𝟙_ _) (𝟙_ _)))
```

## New

```lean
private theorem poincareMap_isIso_aux
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G)
    {P : C ⥤ D} {R : D ⥤ C} (adj' : P ⊣ R)
    (pf : curriedTensorInsertFunctor₁ P ⟶
      curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)
    {T : C} (pur : R.obj (𝟙_ D) ≅ T)
    [∀ B, IsIso ((pf.app (𝟙_ C)).app B)] :
    IsIso (Verdier.poincareMap adj adj' pf pur) := by
  have := Verdier.isIso_exchange_of_isIso adj adj' pf (𝟙_ C) (𝟙_ D)
  unfold Verdier.poincareMap
  infer_instance

theorem isIso_poincareMap : IsIso (poincareMap ℓ p d) := by
  exact poincareMap_isIso_aux
    (boundedConstructibleUpperStarLowerStarAdjunction _ ℓ p)
    (boundedConstructibleUpperShriekAdjunction _ ℓ p)
    (boundedConstructibleExceptionalProjection _ ℓ p)
    (boundedConstructibleSmoothPurityIso ℓ p d)
```

## Users

`tools/downstream.py` cannot index the absent quarantined module. A direct
import search over all current and quarantined Lean sources identifies the
consumer below. No existing declaration type or value used in a public
definition changes. No target semantic review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.Poincare | J3 | Restore archive; repair theorem proof only. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Byte-identical compile input; no source change. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Byte-identical compile input; no source change. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same public declarations and maps; no adaptation. |

## Status

landed 20261024T190117-L-3941029 2026-10-24 (merge of deliver/J3/WeilConjectures.PoincareDuality.Poincare)
