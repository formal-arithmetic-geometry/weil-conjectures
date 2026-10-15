# AlgebraicGeometry.Etale.abelianDerivedBaseChangeTransformation

## Reason

Repair of the returned delivery: the current repository includes A4's landed
`abelianDerivedBaseChangeTransformation` and defines the arrow as its component.
Start from that current file and retain both public signatures and the arrow's
component definition verbatim. Refactor the natural transformation's body into the
mate of the inverse-image square. This preserves the naturality interface used by
`BoundedBelowDerivedSmoothBaseChange` and permits the bounded-below compatibility
proof to compile without expanding the direct-image composite.

The fully proved private `abelianDerivedBaseChangeArrow_eq_pushforward_formula`
recovers the unit/comparison/counit component formula. The additional private
`abelianDerivedBaseChangeTransformation_eq_pushforward` identifies the new mate
with A4's full functor-category composite, verbatim below. Thus both definitions
retain their mathematical value. No axiom, postponed proof or arbitrary witness
is introduced. All existing signatures and public imports are identical.

The changed module is unclaimed. No module held by another group is changed.
Dependent target statement review reopens because the definition body changes;
the explicit equality is the evidence for unchanged meaning. Challenge signatures
are untouched. Unchanged current callers are validated in scratchpad copies.

## Old

```lean
noncomputable def abelianDerivedBaseChangeTransformation {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g) :
    R(lowerStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} f) ⟶
      D(upperStar AddCommGrpCat.{u + 1} e) ⋙ R(lowerStar AddCommGrpCat.{u + 1} h) := by
  let E := D(upperStar AddCommGrpCat.{u + 1} e)
  let U := R(lowerStar AddCommGrpCat.{u + 1} e)
  let G := R(lowerStar AddCommGrpCat.{u + 1} g)
  let H := R(lowerStar AddCommGrpCat.{u + 1} h)
  let Q := R(lowerStar AddCommGrpCat.{u + 1} f)
  let F := D(upperStar AddCommGrpCat.{u + 1} f)
  let c : U ⋙ G ⟶ H ⋙ Q :=
    (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom ≫
      (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w.symm).hom ≫
      (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv
  let β : G ⟶ E ⋙ (H ⋙ Q) :=
    (Functor.leftUnitor G).inv ≫
      Functor.whiskerRight
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e).unit G ≫
      (Functor.associator E U G).hom ≫ Functor.whiskerLeft E c
  exact Functor.whiskerRight β F ≫ (Functor.associator E (H ⋙ Q) F).hom ≫
    Functor.whiskerLeft E ((Functor.associator H Q F).hom ≫
      Functor.whiskerLeft H
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit ≫
      (Functor.rightUnitor H).hom)

/-- The unbounded abelian exchange arrow. Exact inverse image is applied termwise;
right direct image is the total K-injective derived functor. The composition comparisons
are conjugates of the termwise inverse-image comparisons. The formula is the unit for `e`,
the direct-image square comparison, then the counit for `f`, as in the node.
Source: blueprint sk-def-bc; Stacks Project, Tag 0EZR and Tag 0D6G
(blueprint: sbc-def-base-change-map). -/
noncomputable def abelianDerivedBaseChangeArrow {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D(upperStar AddCommGrpCat.{u + 1} f).obj
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj K) ⟶
      R(lowerStar AddCommGrpCat.{u + 1} h).obj
        (D(upperStar AddCommGrpCat.{u + 1} e).obj K) :=
  (abelianDerivedBaseChangeTransformation sq).app K
```

## New

```lean
noncomputable def abelianDerivedBaseChangeTransformation {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g) :
    R(lowerStar AddCommGrpCat.{u + 1} g) ⋙ D(upperStar AddCommGrpCat.{u + 1} f) ⟶
      D(upperStar AddCommGrpCat.{u + 1} e) ⋙ R(lowerStar AddCommGrpCat.{u + 1} h) :=
  (mateEquiv (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h)
    (TwoSquare.mk _ _ _ _
      (((Functor.mapDerivedCategoryNatIso
          (upperStarComp AddCommGrpCat.{u + 1} h f (e ≫ g) sq.w.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} e g) ≪≫
          Functor.mapDerivedCategoryCompIso _ _)).hom))).natTrans

/-- The unbounded abelian exchange arrow. Exact inverse image is applied termwise;
right direct image is the total K-injective derived functor. The composition comparisons
are conjugates of the termwise inverse-image comparisons. The formula is the unit for `e`,
the direct-image square comparison, then the counit for `f`, as in the node.
Source: blueprint sk-def-bc; Stacks Project, Tag 0EZR and Tag 0D6G
(blueprint: sbc-def-base-change-map). -/
noncomputable def abelianDerivedBaseChangeArrow {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D(upperStar AddCommGrpCat.{u + 1} f).obj
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj K) ⟶
      R(lowerStar AddCommGrpCat.{u + 1} h).obj
        (D(upperStar AddCommGrpCat.{u + 1} e).obj K) :=
  (abelianDerivedBaseChangeTransformation sq).app K
```

## Users

The first four rows are all original textual users from
`tools/downstream.py Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets --uses abelianDerivedBaseChangeArrow`.
Its current full import-downstream list has 16 modules; all retain the same public signature.
The fifth row records the new user added in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets | unclaimed | Transformation body uses the equivalent mate; both signatures and arrow body unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | Replaces its sorry with the bounded devissage proof; signature unchanged. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | unclaimed (landed by A4) | No edit; original compiles against the new definition. |
| Sheaf.AlgebraicGeometry.EtaleLocalityBaseChange | unclaimed | No edit; original compiles against the new definition. |
| Sheaf.AlgebraicGeometry.AbelianDerivedExchangePlusCompatibility | B2 (new) | Proves restriction compatibility and equality with the original formula. |

## Status

landed 20261015T174646-L-626596 2026-10-15 (merge of deliver/B2/Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange)
