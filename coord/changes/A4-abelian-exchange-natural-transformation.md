# AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow

## Reason

The old pointwise definition forces a proof of its naturality to repeatedly expand
unbounded derived functors and their localized composition/adjunction terms. A direct
component calculation reached Lean's deterministic kernel timeout (58 seconds), even
when naturality was first proved abstractly. This prevents the truncation comparison
square from compiling within the single-file limit.

Construct the exact same composite in the functor category, using whiskering,
associators and unitors, then evaluate it at K. Naturality is now the natural
transformation's naturality field; the item compiles in seconds. All data are constructed
from the existing canonical unit, the same three comparison maps, and the canonical
counit. Nothing is chosen from an existence theorem. Expanding components and applying
functoriality, map_id and categorical identity/associativity laws recovers the old
formula, with the same map directions and the same sq.w.symm comparison.

The module was unclaimed at preparation. Its existing signatures and public imports
are preserved. No other module needs an adaptation. This changes a definition used by
target statements and therefore **reopens their statement review**, as required by
AGENTS.md section 4 and the stage-3 brief. No Challenge.lean declaration is changed.

## Old

```lean
noncomputable def abelianDerivedBaseChangeArrow {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    D(upperStar AddCommGrpCat.{u + 1} f).obj
      (R(lowerStar AddCommGrpCat.{u + 1} g).obj K) ⟶
      R(lowerStar AddCommGrpCat.{u + 1} h).obj
        (D(upperStar AddCommGrpCat.{u + 1} e).obj K) :=
  D(upperStar AddCommGrpCat.{u + 1} f).map
    (R(lowerStar AddCommGrpCat.{u + 1} g).map
        ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} e).unit.app K) ≫
      (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} e g).hom.app _ ≫
      (rightDerivedLowerStarCongr AddCommGrpCat.{u + 1} sq.w.symm).hom.app _ ≫
      (rightDerivedLowerStarComp AddCommGrpCat.{u + 1} h f).inv.app _) ≫
    (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app _

```

## New

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

## Users

The complete transitive downstream list from tools/downstream.py is included below.
Textual direct users of the changed declaration are the defining module,
BoundedAllowableTorsionSmoothBaseChange, BoundedBelowDerivedSmoothBaseChange and
EtaleLocalityBaseChange. Other rows retain their statements and imports; the canonical
morphism they refer to is mathematically the same.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets | unclaimed | Definition body refactored; transformation added. No postponed data or new holes. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | A4 | Item proof now uses transformation naturality; compiled against refactored definition. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeMapNaturality | C1 | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleLocalityBaseChange | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleSetDegreeZeroFlatBaseChange | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.FieldFailureOfCumulativeBaseChange | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralPushforwardBaseChangeArrow | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.IntegralSurjectiveTargetBaseChange | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.UnboundedBaseChangeComposition | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.Targets.EtaleSmooth | C1 | Same canonical exchange arrow; no signature changes or adaptation required. |
| Sheaf.Targets.EtaleSmoothRing | A2 | Same canonical exchange arrow; no signature changes or adaptation required. |
| TargetsCheck | unclaimed | Same canonical exchange arrow; no signature changes or adaptation required. |

## Status

landed 20261015T154149-L-157907 2026-10-15 (merge of deliver/A4/Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange)
