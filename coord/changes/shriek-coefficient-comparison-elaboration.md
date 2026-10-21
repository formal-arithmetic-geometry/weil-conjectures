# AlgebraicGeometry.ProEtale.shriekCoefficientCompactificationIso

## Reason

Backward inference of the existing long isomorphism composite expands geometric
functor definitions and exceeds the single-file limit. Name the extension-by-zero,
pushforward, and transport functors, and type the two comparison isomorphisms
explicitly. The construction is the same associator/direct-image/open-extension
composite, with the same orientation and coefficients. All public signatures and
all subsequent definitions remain unchanged. Local proof elaboration respects
transparency after the ambient object properties have been elaborated.

## Old

```lean
noncomputable def shriekCoefficientCompactificationIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        shriekCoefficientTransport e Y ≅
      shriekCoefficientTransport e X ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj := by
  letI : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  letI (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  letI (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap e.inv.hom T)).symm
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (CondensedRing.derivedComapLowerStarIso e.inv.hom c.obj.obj.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso
          (CondensedRing.comapOpenImmersionLowerShriekIso e.inv.hom c.obj.obj.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _
```

## New

```lean
noncomputable def shriekCoefficientCompactificationIso
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification.BoundaryCompactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c.obj.obj ⋙
        shriekCoefficientTransport e Y ≅
      shriekCoefficientTransport e X ⋙
        CondensedRing.rightDerivedLowerShriekOfCompactification Λ' c.obj.obj := by
  have : IsIso e.inv.hom := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  letI (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) :=
    inferInstanceAs (IsIso ((upperStarFromPoint T).map e.inv.hom))
  letI (T : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e.inv.hom T)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv
      (coefficientMap e.inv.hom T)).symm
  let J := CondensedRing.openImmersionLowerShriek Λ c.obj.obj.i
  let J' := CondensedRing.openImmersionLowerShriek Λ' c.obj.obj.i
  let P := CondensedRing.lowerStar Λ c.obj.obj.g
  let P' := CondensedRing.lowerStar Λ' c.obj.obj.g
  let UZ := shriekCoefficientTransport e c.obj.obj.Z
  let d : P.rightDerivedFunctor ⋙ shriekCoefficientTransport e Y ≅
      UZ ⋙ P'.rightDerivedFunctor :=
    CondensedRing.derivedComapLowerStarIso e.inv.hom c.obj.obj.g
  let j : J.mapDerivedCategory ⋙ UZ ≅
      shriekCoefficientTransport e X ⋙ J'.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso J (Mod.comap
      (coefficientMap e.inv.hom c.obj.obj.Z))).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (CondensedRing.comapOpenImmersionLowerShriekIso e.inv.hom c.obj.obj.i) ≪≫
      Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom X)) J'
  exact Functor.associator J.mapDerivedCategory P.rightDerivedFunctor
      (shriekCoefficientTransport e Y) ≪≫
    Functor.isoWhiskerLeft J.mapDerivedCategory d ≪≫
    (Functor.associator J.mapDerivedCategory UZ P'.rightDerivedFunctor).symm ≪≫
    Functor.isoWhiskerRight j P'.rightDerivedFunctor ≪≫
    Functor.associator (shriekCoefficientTransport e X) J'.mapDerivedCategory
      P'.rightDerivedFunctor
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ShriekCoefficientIsomorphism | M2 | Same canonical comparison; no consumer adaptation |

`tools/downstream.py Sheaf.Paper.ShriekCoefficientIsomorphism
--uses shriekCoefficientCompactificationIso` found zero downstream modules and
only the uses in this module. No target statement or definition meaning changes.

## Status

landed 20261021T111324-L-73876 2026-10-21 (merge of deliver/M2/Sheaf.Paper.ShriekCoefficientIsomorphism)
