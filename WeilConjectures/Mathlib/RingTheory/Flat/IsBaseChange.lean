/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change of an ideal along a flat ring map

Along a flat ring map `R → S`, the extended ideal `I S` is the base change `S ⊗[R] I` of `I`.

## Main statements

- `Algebra.isBaseChange_idealMap`
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- Along a flat ring map `R → S`, the extended ideal `I S` is the base change of `I`. -/
theorem isBaseChange_idealMap [Module.Flat R S] (I : Ideal R) :
    IsBaseChange S (Algebra.idealMap S I) := by
  have hinj : Function.Injective ((Algebra.idealMap S I).liftBaseChange S) := by
    have h : ((I.map (algebraMap R S)).subtype.restrictScalars R).comp
        (((Algebra.idealMap S I).liftBaseChange S).restrictScalars R) =
        (_root_.TensorProduct.rid R S).toLinearMap.comp (I.subtype.lTensor S) := by
      ext s x
      simp [Algebra.smul_def, mul_comm]
    have : Function.Injective (I.subtype.lTensor S) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    refine fun a b hab ↦ this ?_
    have := congr($h a)
    have := congr($h b)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_coe] at *
    apply (_root_.TensorProduct.rid R S).injective
    rw [← ‹(_ : S) = (_root_.TensorProduct.rid R S) ((I.subtype.lTensor S) a)›,
      ← ‹(_ : S) = (_root_.TensorProduct.rid R S) ((I.subtype.lTensor S) b)›, hab]
  have hsurj : Function.Surjective ((Algebra.idealMap S I).liftBaseChange S) := by
    rintro ⟨y, hy⟩
    refine Submodule.span_induction
      (p := fun y hy ↦ ∃ a, (Algebra.idealMap S I).liftBaseChange S a = ⟨y, hy⟩) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨1 ⊗ₜ ⟨x, hx⟩, by ext; simp⟩
    · exact ⟨0, by ext; simp⟩
    · rintro y z hy hz ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
    · rintro s y hy ⟨a, ha⟩
      exact ⟨s • a, by rw [map_smul, ha]; rfl⟩
  exact .of_equiv (.ofBijective _ ⟨hinj, hsurj⟩) fun x ↦ by simp

end Algebra
