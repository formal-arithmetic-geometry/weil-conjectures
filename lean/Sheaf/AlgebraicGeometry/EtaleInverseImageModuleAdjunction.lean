/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Inverse image of modules on small étale sites

Source: Stacks Project, Modules on Sites, Tags 03D1, 03D2 and 03D3
(blueprint: lem-weil-pbc-inverse-image-module-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inverse image transports the scalar action and the abelian adjunction restricts to modules.
Source: Stacks Project, Tags 03D1--03D3
(blueprint: lem-weil-pbc-inverse-image-module-adjunction).

Proof:
1. By lem-weil-pbc-etale-inverse-image-algebraic-structures and
   lem-weil-pbc-sheaf-algebraic-structures-objects, inverse image preserves products and
   transports the ring and group operations. Apply it to the module axioms to obtain
   the displayed action. Direct image is sectionwise, with restriction of scalars along
   the ring unit (03D1, 03D2); both constructions preserve linear maps.
2. Naturality of the set unit at the scalar action, together with its compatibility with
   product projections, proves that the abelian unit is linear (the square in 03D3).
3. Naturality of the counit at the scalar action proves that it is linear: on the first
   product projection use the triangle identity, and on the second use counit naturality.
   This supplies the implication omitted in 03D3.
4. By lem-weil-pbc-adjunct-counit-identity, the adjoint of alpha is R(alpha) after the
   unit, and alpha is L(beta) followed by the counit. Steps 1--3 prove both implications.
5. Restrict the abelian hom equivalence to the subsets of linear maps. Its naturality
   gives the module adjunction; its unit and counit are the linear maps of steps 2--3.
   The module category is def-weil-sheaf-of-modules-category. -/
theorem etaleInverseImageModuleAdjunction (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1}) :
    let L := Scheme.etaleSetPullback f
    let La := Etale.upperStar AddCommGrpCat.{u + 1} f
    let a := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
    let FaU := sheafForget (D := AddCommGrpCat.{u + 1}) U.smallEtaleTopology
    let FaV := sheafForget (D := AddCommGrpCat.{u + 1}) V.smallEtaleTopology
    let FrU := sheafForget (D := CommRingCat.{u + 1}) U.smallEtaleTopology
    let FrV := sheafForget (D := CommRingCat.{u + 1}) V.smallEtaleTopology
    let b := MorphismProperty.Over.pullback @Etale ⊤ f
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous b
      (Type (u + 1)) (V.smallGrothendieckTopology @Etale)
      (U.smallGrothendieckTopology @Etale)
    let Rr := b.sheafPushforwardContinuous CommRingCat.{u + 1}
      (V.smallGrothendieckTopology @Etale) (U.smallGrothendieckTopology @Etale)
    ∃ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let eta := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (ar.unit.app O)
    let RM := SheafOfModules.pushforward.{u + 1}
      (J := V.smallGrothendieckTopology @Etale)
      (K := U.smallGrothendieckTopology @Etale) (F := b) eta
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    let FU := SheafOfModules.toSheaf.{u + 1} OR
    ∃ (ea : La ⋙ FaU ≅ FaV ⋙ L)
      (LM : SheafOfModules.{u + 1} OV ⥤ SheafOfModules.{u + 1} OR)
      (e : LM ⋙ FU ≅ FV ⋙ La) (am : LM ⊣ RM),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) ∧
      (∀ G : SheafOfModules.{u + 1} OV,
        let iG := (FaU.mapIso (e.app G)) ≪≫ ea.app (FV.obj G)
        ∃ (muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ FaV.obj (FV.obj G))
          (muU : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
            FaU.obj (FU.obj (LM.obj G))),
          (∀ (W : V.Etaleᵒᵖ)
              (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
            muV.hom.app W x =
              @SMul.smul (OV.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
              ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FrV.obj O).hom.app W x : OV.obj.obj W)
              ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
                FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) ∧
          (∀ (W : U.Etaleᵒᵖ)
              (x : ((FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G)))).obj.obj W),
            muU.hom.app W x =
              @SMul.smul (OR.obj.obj W) ((LM.obj G).val.obj W)
                ((LM.obj G).val.obj W).isModule.toSMul
              ((prod.fst : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
                FrU.obj (Lr.obj O)).hom.app W x : OR.obj.obj W)
              ((prod.snd : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj (FU.obj (LM.obj G))) ⟶
                FaU.obj (FU.obj (LM.obj G))).hom.app W x : (LM.obj G).val.obj W)) ∧
          L.map muV = prodComparison L (FrV.obj O) (FaV.obj (FV.obj G)) ≫
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom) ∧
      (∀ (G : SheafOfModules.{u + 1} OV) (F : SheafOfModules.{u + 1} OR)
          (alpha : La.obj (FV.obj G) ⟶ FU.obj F),
        (∃ h : LM.obj G ⟶ F, FU.map h = e.hom.app G ≫ alpha) ↔
          ∃ k : G ⟶ RM.obj F, FV.map k = a.homEquiv (FV.obj G) (FU.obj F) alpha) ∧
      (∀ (G : SheafOfModules.{u + 1} OV) (F : SheafOfModules.{u + 1} OR)
          (h : LM.obj G ⟶ F),
        FV.map (am.homEquiv G F h) =
          a.homEquiv (FV.obj G) (FU.obj F) (e.inv.app G ≫ FU.map h)) ∧
      (∀ G : SheafOfModules.{u + 1} OV,
        FV.map (am.unit.app G) =
          a.unit.app (FV.obj G) ≫ (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
            (e.inv.app G)) ∧
      (∀ F : SheafOfModules.{u + 1} OR,
        FU.map (am.counit.app F) = e.hom.app (RM.obj F) ≫ a.counit.app (FU.obj F)) := by
  sorry

end AlgebraicGeometry
