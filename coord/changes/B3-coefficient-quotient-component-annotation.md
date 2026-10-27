# coefficientOrdinaryQuotientComponent

## Reason

Factor the ordinary quotient components through the explicitly constructed natural mate
`coefficientQuotientNatTrans`. The original component formula is its defining projection,
so the new body is definitionally equal to the old body. This prevents the large chosen
scalar-extension object from unfolding again in the naturality proof. The new public
helper is attached to the item's existing DAG node; it contains no postponed data or proof.

## Old

```lean
noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  ((scalarReductionExtension_adjunction l E W m).choose.homEquiv _ _).symm
    ((scalarReductionExtension_adjunction l E W n).choose.unit.app M ≫
      (eqToIso (coefficientRestrictionComp l E W h)).inv.app
        ((scalarReductionExtension l E W n).obj M))
```

## New

```lean
noncomputable def coefficientQuotientNatTrans
    {A : Type a} {B : Type b} {C : Type c}
    [Category.{v} A] [Category.{w} B] [Category.{r} C]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {F' : A ⥤ C} {G' : C ⥤ A} (adj' : F' ⊣ G')
    (U : C ⥤ B) (e : U ⋙ G ≅ G') : F ⟶ F' ⋙ U where
  app M := (adj.homEquiv M (U.obj (F'.obj M))).symm
    (adj'.unit.app M ≫ e.inv.app (F'.obj M))
  naturality {M N} f := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hn : f ≫ adj'.unit.app N = adj'.unit.app M ≫ G'.map (F'.map f) :=
      adj'.unit.naturality f
    erw [← Category.assoc, hn]
    exact (Category.assoc _ _ _).trans
      ((congrArg (adj'.unit.app M ≫ ·) (e.inv.naturality (F'.map f))).trans
        (Category.assoc _ _ _).symm)

noncomputable def coefficientOrdinaryQuotientComponent {m n : ℕ} (h : n ≤ m)
    (M : scalarReductionSource l E W) :
    (scalarReductionExtension l E W m).obj M ⟶
      (normalizedDVRModuleRes l E W h).obj ((scalarReductionExtension l E W n).obj M) :=
  (coefficientQuotientNatTrans
    (scalarReductionExtension_adjunction l E W m).choose
    (scalarReductionExtension_adjunction l E W n).choose
    (normalizedDVRModuleRes l E W h)
    (eqToIso (coefficientRestrictionComp l E W h))).app M
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | B3 | Definitional refactoring; all component maps and their types remain the same. |

`tools/downstream.py Sheaf.Paper.CoefDerivedSystemEvaluationCalculus --uses
coefficientOrdinaryQuotientComponent` finds no textual user outside the item. No other
module requires adaptation. The item's ordinary quotient existence theorem is proved
from the helper's naturality and component formula. No target statement changes.

## Status

landed 20261022T145606-L-2021248 2026-10-22 (merge of deliver/B3/Sheaf.Paper.CoefDerivedSystemEvaluationCalculus)
