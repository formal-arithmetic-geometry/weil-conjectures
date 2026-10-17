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
    refine AlgEquiv.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
    simp
  map_mul' g h := by
    refine AlgEquiv.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
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
  let := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
  induction x with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add]
  | tmul a l => rfl

lemma smulCommClass_rightTensorAction :
    letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
    SMulCommClass G B₁ (B₁ ⊗[B] L) :=
  letI := rightTensorAction (B := B) (B₁ := B₁) (L := L) G
  ⟨fun g b x ↦ map_smul (rightTensorAlgAut (B := B) (B₁ := B₁) (L := L) G g) b x⟩

section Cover

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B B₁ Bk L : Type*} [CommRing B] [CommRing B₁] [Algebra B B₁] [CommRing Bk]
  [Algebra B Bk] [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]

/-- The map `B₁ ⊗[B] B_K → B₁ ⊗[B] L`. -/
noncomputable abbrev coverMap : B₁ ⊗[B] Bk →ₐ[B₁] B₁ ⊗[B] L :=
  Algebra.TensorProduct.map (AlgHom.id B₁ B₁) (IsScalarTower.toAlgHom B Bk L)

set_option linter.flexible false in
-- The final `simp` unfolds the local definitions of the two inverse maps.
/-- `B₁ ⊗[B] L` is the base change of `L` along `B_K → B₁ ⊗[B] B_K`. -/
noncomputable def coverEquiv :
    letI := (coverMap (B := B) (B₁ := B₁) (Bk := Bk) (L := L)).toRingHom.toAlgebra
    (B₁ ⊗[B] Bk) ⊗[Bk] L ≃ₐ[B₁ ⊗[B] Bk] B₁ ⊗[B] L :=
  letI := (coverMap (B := B) (B₁ := B₁) (Bk := Bk) (L := L)).toRingHom.toAlgebra
  letI : Algebra Bk (B₁ ⊗[B] L) :=
    ((algebraMap (B₁ ⊗[B] Bk) (B₁ ⊗[B] L)).comp (algebraMap Bk (B₁ ⊗[B] Bk))).toAlgebra
  haveI : IsScalarTower Bk (B₁ ⊗[B] Bk) (B₁ ⊗[B] L) := .of_algebraMap_eq' rfl
  let g : L →ₐ[Bk] B₁ ⊗[B] L :=
    { (Algebra.TensorProduct.includeRight : L →ₐ[B] B₁ ⊗[B] L) with
      commutes' := fun c ↦ rfl }
  let F : (B₁ ⊗[B] Bk) ⊗[Bk] L →ₐ[B₁ ⊗[B] Bk] B₁ ⊗[B] L :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ ↦ Commute.all _ _
  let Hl : B₁ →ₐ[B] (B₁ ⊗[B] Bk) ⊗[Bk] L :=
    (Algebra.TensorProduct.includeLeft (S := B) :
      B₁ ⊗[B] Bk →ₐ[B] (B₁ ⊗[B] Bk) ⊗[Bk] L).comp
      (Algebra.TensorProduct.includeLeft : B₁ →ₐ[B] B₁ ⊗[B] Bk)
  let Hr : L →ₐ[B] (B₁ ⊗[B] Bk) ⊗[Bk] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[Bk] (B₁ ⊗[B] Bk) ⊗[Bk] L).restrictScalars B
  let H : B₁ ⊗[B] L →ₐ[B] (B₁ ⊗[B] Bk) ⊗[Bk] L :=
    Algebra.TensorProduct.lift Hl Hr fun _ _ ↦ Commute.all _ _
  let H' : B₁ ⊗[B] L →ₐ[B₁ ⊗[B] Bk] (B₁ ⊗[B] Bk) ⊗[Bk] L :=
    { H.toRingHom with
      commutes' := fun x ↦ by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
          rw [map_add, map_add]
          exact (map_add H.toRingHom _ _).trans (congrArg₂ (· + ·) hx hy)
        | tmul b c => simp [H, Hl, Hr, RingHom.algebraMap_toAlgebra] }
  AlgEquiv.ofAlgHom F H'
    (AlgHom.ext fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, AlgHom.comp_apply, AlgHom.id_apply] at hx hy ⊢
        rw [hx, hy]
      | tmul b x => simp [F, H', H, Hl, Hr, g, RingHom.algebraMap_toAlgebra])
    (AlgHom.ext fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, AlgHom.comp_apply, AlgHom.id_apply] at hx hy ⊢
        rw [hx, hy]
      | tmul a x =>
        induction a using TensorProduct.induction_on with
        | zero => simp
        | add a a' ha ha' =>
          simp only [TensorProduct.add_tmul, map_add, AlgHom.comp_apply, AlgHom.id_apply]
            at ha ha' ⊢
          rw [ha, ha']
        | tmul b c =>
          simp [F, H', H, Hl, Hr, g, RingHom.algebraMap_toAlgebra]
          rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def,
            Algebra.TensorProduct.right_algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul])

end Cover

end Algebra.TraitSection
