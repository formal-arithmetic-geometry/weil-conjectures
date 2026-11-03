/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSiteColimits

/-! # Tensor products of final-object module sections

Source: Stacks 03EL and sheafification at an algebraically closed point.
(blueprint: lem-sf-point-sections-module-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.PointSectionsTensor
variable (k : Type u) [Field k] [IsAlgClosed k]
  (B : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})

/-- The module sheafification unit is invertible after final-object evaluation.
Source: Stacks 03EL and the split-cover criterion
(blueprint: lem-sf-point-sections-module-tensor).

Proof: the underlying abelian presheaf map is its sheafification unit. Every
cover of the final object contains the identity, so this map is bijective there.
A bijective module morphism is an isomorphism. -/
theorem unit_eval_isIso
    (M : PresheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app M).app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have h := ProEtale.bijective_toSheafify_app_of_iso (Iso.refl (Spec (.of k))) M.presheaf
  have he := congrArg (fun t ↦ t.app (op (ProEt.mk (𝟙 (Spec (.of k))))))
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app (𝟙 _) M)
  rw [← he] at h
  exact h

section Scalars
variable {R S : Type (u + 1)} [CommRing R] [CommRing S]
  (α : R →+* S) (hα : Function.Surjective α) (M N : ModuleCat.{u + 1} S)

/-- Restricting along a surjective ring map leaves tensor products unchanged.
Source: tensor product universal property
(blueprint: lem-sf-point-sections-module-tensor). -/
def scalarTensorIso :
    (ModuleCat.restrictScalars α).obj M ⊗ (ModuleCat.restrictScalars α).obj N ≅
      (ModuleCat.restrictScalars α).obj (M ⊗ N) := by
  letI : Algebra R S := α.toAlgebra
  letI : Module R M := Module.compHom M α
  letI : Module R N := Module.compHom N α
  letI : SMulCommClass S R M := ⟨fun s r x ↦ by
    change s • (α r • x) = α r • s • x
    rw [smul_smul, smul_smul, mul_comm]⟩
  letI : SMulCommClass R R M := inferInstance
  letI : TensorProduct.CompatibleSMul R S M N := ⟨fun s x y ↦ by
    obtain ⟨r, rfl⟩ := hα s
    exact TensorProduct.smul_tmul r x y⟩
  letI : TensorProduct.CompatibleSMul S R M N := ⟨fun r x y ↦ by
    change (α r • x) ⊗ₜ[S] y = x ⊗ₜ[S] (α r • y)
    exact TensorProduct.smul_tmul (α r) x y⟩
  exact (TensorProduct.equivOfCompatibleSMul S R R M N).toModuleIso

/-- The scalar tensor isomorphism preserves pure tensors.
Source: tensor product universal property
(blueprint: lem-sf-point-sections-module-tensor).

Proof: both maps in the compatible-scalar equivalence send a pure tensor to
that same tensor, by their defining tensor lifts. -/
theorem scalarTensorIso_tmul (x : M) (y : N) :
    letI : Module R M := Module.compHom M α
    letI : Module R N := Module.compHom N α
    (scalarTensorIso α hα M N).hom (x ⊗ₜ[R] y) = x ⊗ₜ[S] y := by
  rfl
end Scalars

end WeilConjectures.PointSectionsTensor
