/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# The canonical base-change map for sets and unbounded abelian sheaves

Source: blueprint, sec-smooth-base-change, sk-def-bc, and Stacks Project, Tag 0EZR
(blueprint: sbc-def-base-change-map).

The module-coefficient map remains `Etale.derivedBaseChangeMap`. These helpers supply
its set-valued and unbounded abelian versions without imposing monoidal coefficients.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The inverse-image/direct-image adjunction for sets on small etale sites.
Source: Stacks Project, Sites, Tag 00WX (blueprint: sbc-def-base-change-map). -/
noncomputable def setUpperLowerAdjunction {X S : Scheme.{u}} (f : X ⟶ S) :
    Scheme.etaleSetPullback f ⊣ lowerStar (Type (u + 1)) f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
    (S.smallGrothendieckTopology @Etale) (X.smallGrothendieckTopology @Etale)

/-- The set-valued exchange arrow: pull back the unit for `e`, use the canonical
pushforward composition comparisons, then the counit for `f`. This is the inverse mate
of the direct-image square comparison, equivalently the counit-transpose description.
Source: Stacks Project, Tag 0EZR, proof of (1) (blueprint: sbc-def-base-change-map). -/
noncomputable def setBaseChangeArrow {X Y S T : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    (Scheme.etaleSetPullback f).obj ((lowerStar (Type (u + 1)) g).obj F) ⟶
      (lowerStar (Type (u + 1)) h).obj ((Scheme.etaleSetPullback e).obj F) :=
  (Scheme.etaleSetPullback f).map
    ((lowerStar (Type (u + 1)) g).map ((setUpperLowerAdjunction e).unit.app F) ≫
      (lowerStarComp (Type (u + 1)) e g).hom.app _ ≫
      (lowerStarComp (Type (u + 1)) h f (e ≫ g) sq.w.symm).inv.app _) ≫
    (setUpperLowerAdjunction f).counit.app _

/-- The unbounded abelian exchange as a natural transformation. The unit for e,
pushforward composition comparisons, and counit for f are composed as natural
transformations, so naturality does not require expanding any derived functor.
Source: blueprint sk-def-bc; Stacks Project, Tags 0EZR and 0D6G
(blueprint: sbc-def-base-change-map). -/
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

end AlgebraicGeometry.Etale
