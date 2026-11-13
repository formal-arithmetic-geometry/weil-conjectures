/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageScalarDistributivityLeft
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageScalarDistributivityRight

/-! # Distributivity of the transported scalar action

## References

* Stacks Project, Tag 03D2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The transported scalar action on the inverse image is distributive in both variables
(Stacks, Tag 03D2). -/
theorem etaleInverseImageScalarDistributivity (U V : Scheme.{u}) (f : U ⟶ V)
    (O : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
    [PreservesFiniteLimits (Scheme.etaleSetPullback f)] :
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
    ∀ (ea : La ⋙ FaU ≅ FaV ⋙ L),
      (∀ (G : Sheaf V.smallEtaleTopology CommRingCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology CommRingCat.{u + 1}) (h : Lr.obj G ⟶ F),
        FrV.map (ar.homEquiv G F h) =
          aS.homEquiv (FrV.obj G) (FrU.obj F) (er.inv.app G ≫ FrU.map h)) ∧
      (∀ (G : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
          (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) (h : La.obj G ⟶ F),
        FaV.map (a.homEquiv G F h) =
          aS.homEquiv (FaV.obj G) (FaU.obj F) (ea.inv.app G ≫ FaU.map h)) →
    ∀ G : SheafOfModules.{u + 1} OV,
    ∀ muV : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶ (FaV.obj (FV.obj G)),
      (∀ (W : V.Etaleᵒᵖ) (x : ((FrV.obj O) ⨯ (FaV.obj (FV.obj G))).obj.obj W),
        muV.hom.app W x =
          @SMul.smul (O.obj.obj W) (G.val.obj W) (G.val.obj W).isModule.toSMul
            ((prod.fst : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FrV.obj O).hom.app W x : O.obj.obj W)
            ((prod.snd : (FrV.obj O) ⨯ (FaV.obj (FV.obj G)) ⟶
              FaV.obj (FV.obj G)).hom.app W x : G.val.obj W)) →
    let A := La.obj (FV.obj G)
    let mu := prod.map (er.hom.app O) (ea.hom.app (FV.obj G)) ≫
      inv (prodComparison L (FrV.obj O) (FaV.obj (FV.obj G))) ≫
      L.map muV ≫ ea.inv.app (FV.obj G)
    let e : (FrU.obj (Lr.obj O)) ⨯ (FaU.obj A) ≅
        (FrU.obj (Lr.obj O)) ⊗ (FaU.obj A) :=
      (limit.isLimit _).conePointUniqueUpToIso
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
    let act : ∀ W : U.Etaleᵒᵖ, OR.obj.obj W → A.obj.obj W → A.obj.obj W :=
      fun W r x ↦ (e.inv ≫ mu).hom.app W (r, x)
    ∀ W : U.Etaleᵒᵖ,
      (∀ (r : OR.obj.obj W) (x y : A.obj.obj W),
        act W r (x + y) = act W r x + act W r y) ∧
      (∀ (r s : OR.obj.obj W) (x : A.obj.obj W),
        act W (r + s) x = act W r x + act W s x)
    := by
  dsimp only
  intro Lr ar er ea hcompat G muV hmu W
  exact ⟨etaleInverseImageScalarDistributivity_left U V f O Lr ar er ea hcompat G muV hmu W,
    etaleInverseImageScalarDistributivity_right U V f O Lr ar er ea hcompat G muV hmu W⟩

end AlgebraicGeometry
