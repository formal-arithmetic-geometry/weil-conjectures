# WeilConjectures.IntegralAugmentedQuotient.theta

## Reason

The direct monomorphic composite triggered approximately 20 seconds of kernel checking
and 29 seconds of final linting in profiling. The packet then exceeded the fixed
60-second compile limit. Express the same three-factor composite first over abstract
categories in a local let, then specialize it. Beta, the source comparison, the order
of composition and every public signature are unchanged. The local let expands to
the old body, so this is a definitionally equal construction. No theorem is assumed
for its data. Proof-local irreducibility settings also prevent accidental unfolding
of pbcIntegralDatum and derived-category infrastructure.

## Old

```lean
def theta (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g) :
    T l E g ⋙ PulledReduction.tres (datum l E) X ≅ V l E g :=
  Functor.isoWhiskerLeft (redR l E Y)
      (Functor.whiskeringRightObjCompIso (pullR l E g) (res l E X)) ≪≫
    Functor.isoWhiskerLeft (redR l E Y)
      ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso d) ≪≫
    (Functor.isoWhiskerRight (beta l E Y).symm (towerPullC l E g))
```

## New

```lean
def theta (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g) :
    T l E g ⋙ PulledReduction.tres (datum l E) X ≅ V l E g :=
  let build (A B C D : Type _) [Category A] [Category B] [Category C] [Category D]
      (F : A ⥤ B) (R : B ⥤ C) (S : A ⥤ D) (G : D ⥤ C)
      (H : A ⥤ ℕᵒᵖ ⥤ A) (K : D ⥤ ℕᵒᵖ ⥤ D)
      (δ : F ⋙ R ≅ S ⋙ G)
      (b : S ⋙ K ≅ H ⋙ (Functor.whiskeringRight ℕᵒᵖ A D).obj S) :
      (H ⋙ (Functor.whiskeringRight ℕᵒᵖ A B).obj F) ⋙
          (Functor.whiskeringRight ℕᵒᵖ B C).obj R ≅
        S ⋙ K ⋙ (Functor.whiskeringRight ℕᵒᵖ D C).obj G :=
    Functor.isoWhiskerLeft H (Functor.whiskeringRightObjCompIso F R) ≪≫
      Functor.isoWhiskerLeft H ((Functor.whiskeringRight ℕᵒᵖ A C).mapIso δ) ≪≫
      Functor.isoWhiskerRight b.symm ((Functor.whiskeringRight ℕᵒᵖ D C).obj G)
  build _ _ _ _ (pullR l E g) (res l E X) (res l E Y) (pullC l E g)
    (redR l E Y) (redC l E Y) d (beta l E Y)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAugmentedQuotientTowers | T8 | Same composite and statement; bounded unfolding. |

`tools/downstream.py Sheaf.Paper.IntegralAugmentedQuotientTowers` lists zero current
Lean importers. The unfinished parent nodes remain; nothing is withdrawn. This is
under Sheaf, and no adopted WeilConjectures source module changes.

## Status

landed 20261025T123935-L-1919141 2026-10-25 (merge of deliver/T8/Sheaf.Paper.IntegralAugmentedQuotientTowers)
