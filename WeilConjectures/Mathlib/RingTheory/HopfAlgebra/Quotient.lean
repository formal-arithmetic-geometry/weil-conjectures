/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.Quotient

/-!
# Convolution products of algebra homomorphisms killing a Hopf ideal, and suprema of Hopf ideals

If two algebra homomorphisms out of a Hopf algebra `A` vanish on a Hopf ideal `I`, then so does
their convolution product: both factor through the quotient Hopf algebra `A ⧸ I`, and the
quotient map is a bialgebra homomorphism.

The supremum of a family of Hopf ideals is a Hopf ideal (`Ideal.isHopfIdeal_sSup`).

## Blueprint

- `sk-d-geometry`: the points of a closed subgroup scheme `V(I)` of an affine group scheme form a
  subgroup.
-/

@[expose] public section

open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommRing B] [Algebra R B]

namespace Ideal.IsHopfIdeal

/-- The zero ideal is a Hopf ideal. -/
instance bot : (⊥ : Ideal A).IsHopfIdeal R where
  counit_eq_zero x hx := by simp_all
  map_mkQ_comul_eq_zero x hx := by
    rw [Submodule.restrictScalars_mem, Ideal.mem_bot] at hx
    rw [hx, map_zero, map_zero]
  antipode_mem x hx := by simp_all

/-- The convolution product of two algebra homomorphisms vanishing on a Hopf ideal vanishes on
it. (blueprint: `sk-d-geometry`) -/
theorem convMul_apply_eq_zero {I : Ideal A} [I.IsHopfIdeal R] {f g : A →ₐ[R] B}
    (hf : ∀ a ∈ I, f a = 0) (hg : ∀ a ∈ I, g a = 0) {a : A} (ha : a ∈ I) :
    (toConv f * toConv g) a = 0 := by
  let q : A →ₐc[R] A ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hf' : f = (Ideal.Quotient.liftₐ I f hf).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  have hg' : g = (Ideal.Quotient.liftₐ I g hg).comp (q : A →ₐ[R] A ⧸ I) := by ext; rfl
  rw [hf', hg', ← AlgHom.convMul_comp_bialgHom_distrib]
  have : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
  simp [this]

/-- The supremum of a family of Hopf ideals is a Hopf ideal. -/
theorem _root_.Ideal.isHopfIdeal_sSup {S : Set (Ideal A)} (hS : ∀ J ∈ S, J.IsHopfIdeal R) :
    (sSup S).IsHopfIdeal R := by
  let D := (sSup S).restrictScalars R
  suffices h : ∀ x ∈ sSup S, Coalgebra.counit (R := R) x = 0 ∧
      TensorProduct.map D.mkQ D.mkQ (Coalgebra.comul x) = 0 ∧
      HopfAlgebra.antipode R x ∈ sSup S from
    { counit_eq_zero := fun x hx ↦ (h x hx).1
      map_mkQ_comul_eq_zero := fun x hx ↦ (h x hx).2.1
      antipode_mem := fun x hx ↦ (h x hx).2.2 }
  intro x hx
  rw [sSup_eq_iSup'] at hx
  induction hx using Submodule.iSup_induction' with
  | mem J x hx =>
    have := hS J J.2
    have hJ : J.1 ≤ sSup S := le_sSup J.2
    refine ⟨Submodule.IsCoideal.counit_eq_zero (I := J.1.restrictScalars R) hx, ?_,
      hJ (IsHopfIdeal.antipode_mem hx)⟩
    let q := (J.1.restrictScalars R).mapQ D LinearMap.id hJ
    have hq : q ∘ₗ (J.1.restrictScalars R).mkQ = D.mkQ := Submodule.mapQ_mkQ _ _ _
    rw [← hq, TensorProduct.map_comp, LinearMap.comp_apply,
      Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := J.1.restrictScalars R) hx, map_zero]
  | zero => simp
  | add x y _ _ hx hy => exact ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1],
      by simpa using add_mem hx.2.2 hy.2.2⟩

end Ideal.IsHopfIdeal
