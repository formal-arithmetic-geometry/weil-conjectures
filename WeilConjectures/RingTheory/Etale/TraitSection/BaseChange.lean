/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Base change of the trait data

Let `R₀ → A₁` be a ring map, `B` an `R₀`-algebra, `B_K` the localization of `B` at the image of
the nonzero elements of `R₀` and `B₁ = B ⊗[R₀] A₁` (an `A₁`-algebra through the second factor).
If every nonzero element of `A₁` divides the image of a nonzero element of `R₀`, then
`B₁ ⊗[B] B_K` is the localization of `B₁` at the nonzero elements of `A₁`
(`Algebra.TraitSection.isLocalization_tensor_of_dvd`).

This is part of the reduction of the trait case of blueprint
`sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]) to a base containing the roots of unity.
-/

@[expose] public section

open TensorProduct

namespace Algebra.TraitSection

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- See the module docstring. -/
theorem isLocalization_tensor_of_dvd {R₀ A₁ B Bk : Type*} [CommRing R₀] [CommRing A₁]
    [Algebra R₀ A₁] [CommRing B] [Algebra R₀ B] [CommRing Bk] [Algebra B Bk]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
    (hdvd : ∀ a ∈ nonZeroDivisors A₁, ∃ r ∈ nonZeroDivisors R₀, a ∣ algebraMap R₀ A₁ r)
    (hR : ∀ r ∈ nonZeroDivisors R₀, algebraMap R₀ A₁ r ∈ nonZeroDivisors A₁) :
    IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[R₀] A₁) (nonZeroDivisors A₁))
      ((B ⊗[R₀] A₁) ⊗[B] Bk) := by
  have hmap (r : R₀) : algebraMap B (B ⊗[R₀] A₁) (algebraMap R₀ B r) =
      algebraMap A₁ (B ⊗[R₀] A₁) (algebraMap R₀ A₁ r) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.right_algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine IsLocalization.of_le_of_exists_dvd
    (Algebra.algebraMapSubmonoid (B ⊗[R₀] A₁)
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))) _ ?_ ?_
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨_, hR r hr, (hmap r).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨r, hr, hdv⟩ := hdvd a ha
    exact ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, by rw [hmap]; exact map_dvd _ hdv⟩

variable {B B₁ L : Type*} [CommRing B] [CommRing B₁] [Algebra B B₁] [CommRing L] [Algebra B L]
  (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G B L]

/-- The action of `G` on `B₁ ⊗[B] L` through the second factor, as a group homomorphism. -/
noncomputable def rightTensorAlgAut : G →* (B₁ ⊗[B] L ≃ₐ[B₁] B₁ ⊗[B] L) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (MulSemiringAction.toAlgEquiv B L g)
  map_one' := by
    refine AlgEquiv.coe_algHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
    simp
  map_mul' g h := by
    refine AlgEquiv.coe_algHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
    simp [mul_smul]

/-- The action of `G` on `B₁ ⊗[B] L` through the second factor. -/
@[instance_reducible]
noncomputable def rightTensorAction : MulSemiringAction G (B₁ ⊗[B] L) :=
  MulSemiringAction.compHom _ (rightTensorAlgAut (B := B) (B₁ := B₁) (L := L) G)

lemma rightTensorAction_smul_tmul (g : G) (a : B₁) (l : L) :
    letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
    g • (a ⊗ₜ[B] l) = a ⊗ₜ[B] (g • l) :=
  rfl

lemma rightTensorAction_smul_eq (g : G) (x : B₁ ⊗[B] L) :
    letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
    g • x = Algebra.TensorProduct.map (AlgHom.id B₁ B₁) (MulSemiringAction.toAlgHom B L g) x := by
  letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
  induction x with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add]
  | tmul a l => rfl

lemma smulCommClass_rightTensorAction :
    letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
    SMulCommClass G B₁ (B₁ ⊗[B] L) :=
  letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
  ⟨fun g b x ↦ map_smul (rightTensorAlgAut (B := B) (B₁ := B₁) (L := L) G g) b x⟩

end Algebra.TraitSection
