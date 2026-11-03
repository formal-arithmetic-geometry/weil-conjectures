/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.CoefficientHeartTowerEtaleMap
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.Reduction.CoefficientHeartTowerQuotientMap

/-! # Compatibility of the actual finite quotient section images

Source: coefficient-heart proof (1), the finite matrices before passage to the limit.
(blueprint: lem-sfb-coefficient-heart-native-section-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {X : Scheme.{u}} {pi : A} {M N : Modules A X}

/-- Pointed finite module sections give the corresponding native quotient square.
Source: coefficient-heart proof (1), the finite matrix of the integral morphism.
(blueprint: lem-sfb-coefficient-heart-native-section-naturality)
Proof: apply naturality of the canonical finite-section image, then apply the abelian
forgetful functor to the supplied module-section square and compose its target image. -/
theorem Reduction.sectionImages_compatibility (R : Reduction A X pi M)
    (S : Reduction A X pi N) (h : M ⟶ N) (n : ℕ) (U : X.Etale)
    (P Q : ModuleCat.{u + 1} A) (tR : P ⟶ (R.etale.obj (op n)).obj.obj (op U))
    (tS : Q ⟶ (S.etale.obj (op n)).obj.obj (op U)) (f : P ⟶ Q)
    (ht : tR ≫ ((R.etaleMap S (R.quotientMap S h)).app (op n)).hom.app (op U) =
      f ≫ tS) :
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map tR ≫ R.sectionImageHom A n U ≫
        ((R.quotientMap S h).app (op n)).hom.hom.app (op ((Scheme.toProEt X).obj U)) =
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map (f ≫ tS) ≫
        S.sectionImageHom A n U := by
  have ht' := congrArg ((forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map) ht
  rw [Functor.map_comp] at ht'
  rw [R.sectionImageHom_natural S h n U, ← Category.assoc]
  change ((forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map tR ≫
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map
        (((R.etaleMap S (R.quotientMap S h)).app (op n)).hom.app (op U))) ≫
      S.sectionImageHom A n U = _
  rw [ht']

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
