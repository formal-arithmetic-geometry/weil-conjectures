# mateOpenPullback and the canonical open-restriction maps

## Reason

Extract the eight existing canonical definitions into `Sheaf.Paper.MateOpenRestrictionMaps` so geometric compact-support lemmas can refer to the specified maps without importing the exceptional-adjoint theorem they prove. The item publicly imports the extracted module. Names, signatures, defining terms, attributes and visibility are unchanged. No target statement or mathematical definition changes. This is an import-cycle repair, not a split to evade compilation limits.

## Old

Defined in `Sheaf.Paper.MateOpenRestriction`:

```lean
def mateOpenPullback {U X : Scheme.{u}} (j : U ⟶ X)
    (h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ U).FullSubcategory :=
  (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ j).mapDerivedCategory) h

def mateOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ U).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ U).ι ⋙
      (openImmersionLowerShriek Λ j).mapDerivedCategory) h

def mateOpenExtensionComp {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)))

def mateOpenSourceLowerShriek {U X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      rightDerivedLowerShriekOfCompactification Λ (c.precomp j) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mateOpenExtensionComp Λ j c.i)
      (lowerStar Λ c.g).rightDerivedFunctor

def mateOpenProperRestriction {Z Z' Y V : Scheme.{u}}
    {a : Z' ⟶ Z} {q : Z' ⟶ V} {p : Z ⟶ Y} {v : V ⟶ Y}
    (sq : CommSq a q p v)
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (upperStar Λ v).mapDerivedCategory.obj ((lowerStar Λ p).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ q).rightDerivedFunctor.obj ((upperStar Λ a).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ q).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ q)).homEquiv _ _
      (((Functor.mapDerivedCategoryCompIso (upperStar Λ v) (upperStar Λ q)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ q v).symm ≪≫
            eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ a p) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ p) (upperStar Λ a)).hom.app
          ((lowerStar Λ p).rightDerivedFunctor.obj B) ≫
        (upperStar Λ a).mapDerivedCategory.map
          (((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).counit.app B))

def mateOpenSquareExtension {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) :
    (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory :=
  mateOpenExtensionComp Λ a c.i ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (by
        congr 1
        exact (c.ofIsPullback_i_fst sq).symm)) ≪≫
    (mateOpenExtensionComp Λ (c.ofIsPullback sq).i (pullback.fst c.g v)).symm

def mateOpenTargetLowerShriek {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (upperStar Λ v).mapDerivedCategory.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((openImmersionLowerShriek Λ a).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj M :=
  (upperStar Λ v).mapDerivedCategory.map
      ((lowerStar Λ c.g).rightDerivedFunctor.map
        ((mateOpenSquareExtension Λ sq c).hom.app M)) ≫
    mateOpenProperRestriction Λ (IsPullback.of_hasPullback c.g v).toCommSq
      ((openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)) ≫
    (lowerStar Λ (pullback.snd c.g v)).rightDerivedFunctor.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
        (pullback.fst c.g v)).unit.app
          ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)))

def mateOpenTrivialLowerShriek {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory :=
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
      (refinementDerivedLowerStarId Λ X) ≪≫
    Functor.rightUnitor _
```

## New

Defined verbatim in `Sheaf.Paper.MateOpenRestrictionMaps` and publicly reexported by `Sheaf.Paper.MateOpenRestriction`:

```lean
def mateOpenPullback {U X : Scheme.{u}} (j : U ⟶ X)
    (h : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      localizingClosureProEtale Λ U ((upperStar Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ U).FullSubcategory :=
  (localizingClosureProEtale Λ U).lift
    ((localizingClosureProEtale Λ X).ι ⋙ (upperStar Λ j).mapDerivedCategory) h

def mateOpenExtension {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
      localizingClosureProEtale Λ X
        ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) :
    (localizingClosureProEtale Λ U).FullSubcategory ⥤
      (localizingClosureProEtale Λ X).FullSubcategory :=
  (localizingClosureProEtale Λ X).lift
    ((localizingClosureProEtale Λ U).ι ⋙
      (openImmersionLowerShriek Λ j).mapDerivedCategory) h

def mateOpenExtensionComp {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (j ≫ i)).mapDerivedCategory :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ j i) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ i) (upperStar Λ j)))

def mateOpenSourceLowerShriek {U X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek Λ j).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification Λ c ≅
      rightDerivedLowerShriekOfCompactification Λ (c.precomp j) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mateOpenExtensionComp Λ j c.i)
      (lowerStar Λ c.g).rightDerivedFunctor

def mateOpenProperRestriction {Z Z' Y V : Scheme.{u}}
    {a : Z' ⟶ Z} {q : Z' ⟶ V} {p : Z ⟶ Y} {v : V ⟶ Y}
    (sq : CommSq a q p v)
    (B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (upperStar Λ v).mapDerivedCategory.obj ((lowerStar Λ p).rightDerivedFunctor.obj B) ⟶
      (lowerStar Λ q).rightDerivedFunctor.obj ((upperStar Λ a).mapDerivedCategory.obj B) :=
  ((derivedUpperStarLowerStarAdjunction Λ q).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ q)).homEquiv _ _
      (((Functor.mapDerivedCategoryCompIso (upperStar Λ v) (upperStar Λ q)).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          ((upperStarComp Λ q v).symm ≪≫
            eqToIso (congrArg (upperStar Λ) sq.w.symm) ≪≫ upperStarComp Λ a p) ≪≫
        Functor.mapDerivedCategoryCompIso (upperStar Λ p) (upperStar Λ a)).hom.app
          ((lowerStar Λ p).rightDerivedFunctor.obj B) ≫
        (upperStar Λ a).mapDerivedCategory.map
          (((derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
            (leftDerivedUpperStarIsoMapDerivedCategory Λ p)).counit.app B))

def mateOpenSquareExtension {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f) :
    (openImmersionLowerShriek Λ a).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ c.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory ⋙
        (openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory :=
  mateOpenExtensionComp Λ a c.i ≪≫
    Functor.mapDerivedCategoryNatIso
      (eqToIso (by
        congr 1
        exact (c.ofIsPullback_i_fst sq).symm)) ≪≫
    (mateOpenExtensionComp Λ (c.ofIsPullback sq).i (pullback.fst c.g v)).symm

def mateOpenTargetLowerShriek {U X V Y : Scheme.{u}}
    {a : U ⟶ X} {q : U ⟶ V} {f : X ⟶ Y} {v : V ⟶ Y}
    [IsOpenImmersion a] [IsOpenImmersion v]
    (sq : IsPullback a q f v) (c : Compactification f)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (upperStar Λ v).mapDerivedCategory.obj
        ((rightDerivedLowerShriekOfCompactification Λ c).obj
          ((openImmersionLowerShriek Λ a).mapDerivedCategory.obj M)) ⟶
      (rightDerivedLowerShriekOfCompactification Λ (c.ofIsPullback sq)).obj M :=
  (upperStar Λ v).mapDerivedCategory.map
      ((lowerStar Λ c.g).rightDerivedFunctor.map
        ((mateOpenSquareExtension Λ sq c).hom.app M)) ≫
    mateOpenProperRestriction Λ (IsPullback.of_hasPullback c.g v).toCommSq
      ((openImmersionLowerShriek Λ (pullback.fst c.g v)).mapDerivedCategory.obj
        ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)) ≫
    (lowerStar Λ (pullback.snd c.g v)).rightDerivedFunctor.map
      (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ
        (pullback.fst c.g v)).unit.app
          ((openImmersionLowerShriek Λ (c.ofIsPullback sq).i).mapDerivedCategory.obj M)))

def mateOpenTrivialLowerShriek {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsOpenImmersion j) ≅
      (openImmersionLowerShriek Λ j).mapDerivedCategory :=
  Functor.isoWhiskerLeft (openImmersionLowerShriek Λ j).mapDerivedCategory
      (refinementDerivedLowerStarId Λ X) ≪≫
    Functor.rightUnitor _
```

## Users

`tools/downstream.py Sheaf.Paper.MateOpenRestriction --uses <name>` was run for every moved name; direct-source searches independently give the same users.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.MateOpenRestriction | F3 | Publicly imports Maps; theorem signatures and the three existing proofs are preserved. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Its two uses of mateOpenTrivialLowerShriek retain the same term through the public import; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Its use of mateOpenTrivialLowerShriek retains the same term through the public import; no adaptation. |

All other downstream modules receive the identical API through the item module. No source-library file is edited.

## Status

landed 20261025T050731-L-3836593 2026-10-25 (merge of deliver/F3/Sheaf.Paper.MateOpenRestriction)
