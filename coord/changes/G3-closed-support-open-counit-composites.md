# AlgebraicGeometry.Etale.openCounitRestrictionLift and closedSupportOpenCounitArrow

## Reason

The direct specializations of the degree-zero comparison and derived counit made
kernel checking of the complete proof exceed the file limit. Define their composites
first for arbitrary exact adjoint functors, then specialize. Both definitions retain
their signatures and are definitionally equal to their old bodies: expanding
`exactRestrictionLift` and `exactCounitComposite` gives precisely those bodies.
The specified adjunction and standard exact-functor comparison are unchanged.

## Old

```lean
noncomputable def openCounitRestrictionLift (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj G ⟶
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
  (_root_.DerivedCategory.singleFunctor _ 0).map ρ.inv ≫
    ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategorySingleFunctor 0).inv.app F

/-- The actual arrow `Dj_! G → F`: apply `Dj_!` to the normalized inverse
restriction map and then apply the counit of the localized original sheaf adjunction.
Source: Stacks 03S3, 095L and 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def closedSupportOpenCounitArrow (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj F :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
      (openCounitRestrictionLift A j F G ρ) ≫
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).counit.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)
```

## New

```lean
section ExactFunctor

variable {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

/-- Transport an inverse comparison to degree zero using the standard exact-functor
comparison. Source: Stacks 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def exactRestrictionLift (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (F : D) (G : C) (ρ : R.obj F ≅ G) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj G ⟶
      R.mapDerivedCategory.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
  (_root_.DerivedCategory.singleFunctor _ 0).map ρ.inv ≫
    (R.mapDerivedCategorySingleFunctor 0).inv.app F

/-- The counit composite after the inverse degree-zero comparison.
Source: Stacks 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def exactCounitComposite {L : C ⥤ D} {R : D ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (F : D) (G : C) (ρ : R.obj F ≅ G) :
    L.mapDerivedCategory.obj ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj F :=
  L.mapDerivedCategory.map (exactRestrictionLift R F G ρ) ≫
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction a).counit.app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)

end ExactFunctor

/-- The inverse restriction isomorphism on degree-zero sheaves, with the standard
exact-functor comparison identifying the target with the derived inverse image.
Source: Stacks 03S3 and 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def openCounitRestrictionLift (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (_root_.DerivedCategory.singleFunctor _ 0).obj G ⟶
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F) :=
  exactRestrictionLift (upperStar (ModuleCat.{u + 1} A) j) F G ρ

/-- The actual arrow `Dj_! G → F`: apply `Dj_!` to the normalized inverse
restriction map and then apply the counit of the localized original sheaf adjunction.
Source: Stacks 03S3, 095L and 015F (blueprint: lem-pur-closed-support-open-counit). -/
noncomputable def closedSupportOpenCounitArrow (A : Type (u + 1)) [CommRing A]
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (ρ : (upperStar (ModuleCat.{u + 1} A) j).obj F ≅ G) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj G) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj F :=
  exactCounitComposite
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j) F G ρ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSupportOpenCounit | G3 | Proved the original theorem with the same statement, using the generic composite lemma. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ClosedSupportOpenCounit --uses
openCounitRestrictionLift closedSupportOpenCounitArrow` reports zero downstream
modules and only this module uses the definitions. A textual scan of both `lean/`
and `quarantine/` likewise found no other use of either declaration. The defining
expressions reduce to the old expressions, so even future callers using their
definitional equations see the same arrows. The target statements do not change;
any target's use of these definitions denotes the same original constructions.
The existing node owns the two generic constructors as part of this construction;
its attachment lists them. No source-library module changes.

## Status

landed 20261024T185755-L-3669292 2026-10-24 (merge of deliver/G3/Sheaf.AlgebraicGeometry.ClosedSupportOpenCounit)
