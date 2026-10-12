/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
/-! # Transporting modules through the etale inverse image

Source: Stacks Project, Tags 03D1 and 03D2
(blueprint: lem-weil-pbc-inverse-image-module-construction). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Construct the module inverse-image functor and its transported scalar action.
Source: Stacks Project, Tags 03D1 and 03D2
(blueprint: lem-weil-pbc-inverse-image-module-construction).

Proof: the hom-equivalence equations pin the ring and abelian comparisons to
the set adjunction. By uniqueness of left adjoints they are the transported lifts of
`etaleInverseImageAlgebraicStructures`, and thus identify the ring and group operations.
For each module,
apply the set inverse image to its action map. Conjugate through the product comparison,
the ring comparison, and the abelian comparison to obtain an action on the abelian
inverse image. The comparisons preserve projections and are natural. Applying the
set inverse image to each module law therefore proves distributivity in both
variables, associativity of scalar multiplication, and the unit law. The resulting
section actions commute with restriction because the transported action is a sheaf
morphism. Applying inverse image to the linearity equation for a module map gives a
linear map between these modules. Identities and composites are preserved by the
abelian inverse-image functor, so these maps define LM. The underlying abelian
comparisons define the natural isomorphism e. Construct muV and muU sectionwise from
the actual scalar multiplication; the definition of the transported action gives
the displayed product-comparison identity. -/
theorem etaleInverseImageModuleConstruction (U V : Scheme.{u}) (f : U ⟶ V)
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
    ∀ (Lr : Sheaf V.smallEtaleTopology CommRingCat.{u + 1} ⥤
        Sheaf U.smallEtaleTopology CommRingCat.{u + 1})
      (ar : Lr ⊣ Rr) (er : Lr ⋙ FrU ≅ FrV ⋙ L),
    let OR := (sheafCompose U.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Lr.obj O)
    let OV := (sheafCompose V.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O
    let FV := SheafOfModules.toSheaf.{u + 1} OV
    let FU := SheafOfModules.toSheaf.{u + 1} OR
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∃ (LM : SheafOfModules.{u + 1} OV ⥤ SheafOfModules.{u + 1} OR)
      (e : LM ⋙ FU ≅ FV ⋙ La),
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
            prod.map (er.inv.app O) iG.inv ≫ muU ≫ iG.hom) := by sorry

end AlgebraicGeometry
