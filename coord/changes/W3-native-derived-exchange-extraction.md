# AlgebraicGeometry.ProEtale.adicDerivedBaseChange

## Reason

The affine and open-chart comparison lemmas need the specified native derived exchange
construction without importing its geometric proper-base-change theorem. Keeping the
construction in the theorem module would create an import cycle. Extract its two
existing definitions into a new foundation module and publicly reexport it from the item.
No data, signatures, names, universes, attributes, or existing public imports change.
No source-library file is edited.

## Old

In `Sheaf.WeilSheaf.GeometricProperBaseChange`:

```lean
def adicDerivedPullSquare (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicUpperStar l g).mapDerivedCategory ⋙ (adicUpperStar l p').mapDerivedCategory ≅
      (adicUpperStar l p).mapDerivedCategory ⋙ (adicUpperStar l v).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The unit--square--counit mate on ordinary native geometric derived categories.
No boundedness, properness, or Weil structure is needed to construct it.
Source: blueprint sk-def-sfb-base-change-morphism.
(blueprint: lem-sf-geometric-native-proper-base-change). -/
def adicDerivedBaseChange (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicLowerStar l p).rightDerivedFunctor ⋙ (adicUpperStar l g).mapDerivedCategory ⟶
      (adicUpperStar l v).mapDerivedCategory ⋙ (adicLowerStar l p').rightDerivedFunctor :=
  (mateEquiv
    (adicUpperStarLowerStarAdjunction l p).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (adicDerivedPullSquare l sq).hom)).natTrans

```

## New

In `Sheaf.WeilSheaf.NativeDerivedBaseChange`, publicly imported by the original module:

```lean
def adicDerivedPullSquare (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicUpperStar l g).mapDerivedCategory ⋙ (adicUpperStar l p').mapDerivedCategory ≅
      (adicUpperStar l p).mapDerivedCategory ⋙ (adicUpperStar l v).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The unit--square--counit mate on ordinary native geometric derived categories.
No boundedness, properness, or Weil structure is needed to construct it.
Source: blueprint sk-def-sfb-base-change-morphism.
(blueprint: def-sf-native-derived-exchange-map). -/
def adicDerivedBaseChange (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicLowerStar l p).rightDerivedFunctor ⋙ (adicUpperStar l g).mapDerivedCategory ⟶
      (adicUpperStar l v).mapDerivedCategory ⋙ (adicLowerStar l p').rightDerivedFunctor :=
  (mateEquiv
    (adicUpperStarLowerStarAdjunction l p).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (adicDerivedPullSquare l sq).hom)).natTrans

```

## Users

`tools/downstream.py --uses AlgebraicGeometry.ProEtale.adicDerivedBaseChange` finds
two actual declaration users (including the defining item), and 198 modules in the
transitive import closure. The unchanged names, signatures and data and the public
reexport preserve every transitive consumer. The sole direct importer is checked
against the delivery without editing it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.WeilSheaf.GeometricProperBaseChange | W3 | publicly reexports the extracted definitions; proves the existing theorem |
| Sheaf.WeilSheaf.NativeBaseChangeForgetComparison | unclaimed in current shared claim records | unchanged consumer of the same exchange map; compiled successfully against this delivery |

No consumer adaptation is needed. The meaning of every target is unchanged.

## Status

landed 20261027T050651-L-251723 2026-10-27 (merge of deliver/W3/Sheaf.WeilSheaf.GeometricProperBaseChange)
