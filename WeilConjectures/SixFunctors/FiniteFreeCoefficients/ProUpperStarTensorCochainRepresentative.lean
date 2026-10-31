/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.ProScalarPullbackCochainData
import all WeilConjectures.AlgebraicGeometry.Upper.UpperStarTensorCochainRepresentative

/-! # The pro-etale upper-star tensor counit on cochain representatives

Source: Stacks Tags 07A4 and 0FPH. Apply the defining two-variable derived
natural-transformation equation, expand its two counits, and transport the
homotopy-category equation through the quotient tensorator.
(blueprint: new-sf-pro-upper-star-tensor-cochain-representative). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
attribute [local instance]
  ProEtale.isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  ProEtale.isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

private theorem pro_tensor_counit_square
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Etale.LaxSquareHδ (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
      (F := (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ))
      (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
      (fun K ↦ (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app K) := by
  intro K M
  have h := Functor.leftDerived₂NatTrans_app_app _
    (ProEtale.derivedTensorLeftDerivedUpperStarCounit (ModuleCat.{u + 1} A) f)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _
    (ProEtale.leftDerivedUpperStarDerivedTensorCounit (ModuleCat.{u + 1} A) f)
    (Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f)) DerivedCategory.Qh) K M
  have e₁ : ((ProEtale.derivedTensorLeftDerivedUpperStarCounit
      (ModuleCat.{u + 1} A) f).app K).app M =
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app K ⊗ₘ
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app M) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ)).obj K)
        (((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ)).obj M) := by
    rw [MonoidalCategory.tensorHom_def]
    dsimp [ProEtale.derivedTensorLeftDerivedUpperStarCounit, ProEtale.derivedTensor]
    rw [Category.assoc]
    rfl
  have e₂ : ((ProEtale.leftDerivedUpperStarDerivedTensorCounit
      (ModuleCat.{u + 1} A) f).app K).app M =
      (Sites.proPull A f).map (Functor.LaxMonoidal.μ DerivedCategory.Qh K M) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit.app (K ⊗ M) := rfl
  have e₃ : ((Functor.postcompose₂MapWhiskeringLeft₂
      (Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
        (ProEtale.upperStar (ModuleCat.{u + 1} A) f)) DerivedCategory.Qh).app K).app M =
      DerivedCategory.Qh.map (Functor.OplaxMonoidal.δ
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomotopyCategory (.up ℤ)) K M) := rfl
  rw [e₁, e₂, e₃] at h
  simp only [Category.assoc] at h
  exact Etale.app_app_comp_of_eq h
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f) rfl

/-- The defining pro-etale tensor counit equation on arbitrary cochain complexes.
Source: Stacks 07A4 and 0FPH.
Proof: the defining derived natural-transformation equation gives the tensor
counit square on homotopy categories. The quotient tensorator is the homotopy
localization tensorator and the homotopy factors have identity components.
The generic cochain tensor-counit transport therefore gives precisely this equation.
(blueprint: new-sf-pro-upper-star-tensor-cochain-representative). -/
theorem pro_upperStar_tensor_cochain_representative
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] {Y X : Scheme.{u}} (f : Y ⟶ X) :
    Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := (ProEtale.upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ))
      (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
      (fun K ↦ (pro_geometric_representative A f).app K) := by
  apply Etale.cochain_tensor_counit_core
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f) (Sites.proPull A f)
    (ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit
    (fun K ↦ (pro_geometric_representative A f).app K)
  · intro K
    exact Etale.representative_quotient
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f) (Sites.proPull A f)
      (ProEtale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctorCounit K
  · exact pro_tensor_counit_square A f

end WeilConjectures.FiniteFreeCoefficients
