/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import WeilConjectures.RingTheory.IntegralClosure.NoetherianApproximation

/-!
# Smooth models over Noetherian normal local subrings

Let `A` be an integrally closed local domain and `B` a smooth `A`-algebra. Then `B` descends to
a smooth algebra over a Noetherian integrally closed local subring `P ⊆ A` dominated by `A`,
which may be chosen to contain any given finite subset of `A`
(`IsLocalRing.exists_subring_smooth_model`). This is the first step of the local version of the
reduction of the spreading theorem (blueprint `sbc-thm-spreading-finite-etale-galois`,
[Stacks 0EZJ]) to a Noetherian base.
-/

@[expose] public section

universe u

open TensorProduct

namespace IsLocalRing

/-- A smooth algebra `B` over an integrally closed local domain `A` descends to a smooth
algebra `B₀` over a Noetherian integrally closed local subring `P ⊆ A` containing a given finite
set `E` and dominated by `A`: `B ≃ A ⊗[P] B₀`. -/
theorem exists_subring_smooth_model {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] {E : Set A} (hE : E.Finite) (B : Type*) [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] :
    ∃ (P : Subring A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra P B₀), E ⊆ P ∧
      IsNoetherianRing P ∧ IsLocalRing P ∧ IsIntegrallyClosed P ∧ IsLocalHom P.subtype ∧
      Algebra.Smooth P B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[P] B₀) := by
  obtain ⟨A₀, B₀, _, _, ⟨s, hs⟩, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg (R := ℤ) A B
  obtain ⟨P, hEP, hnoeth, hloc, hint, hdom⟩ :=
    exists_subring_isNoetherianRing_isIntegrallyClosed (hE.union s.finite_toSet)
  have hle : A₀ ≤ subalgebraOfSubring P := by
    rw [← hs, Algebra.adjoin_le_iff]
    exact fun x hx ↦ hEP (Or.inr hx)
  let : Algebra A₀ P := ((algebraMap A₀ A).codRestrict P fun x ↦ hle x.2).toAlgebra
  have : IsScalarTower A₀ P A := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨P, P ⊗[A₀] B₀, inferInstance, inferInstance, fun x hx ↦ hEP (Or.inl hx), hnoeth, hloc,
    hint, hdom, inferInstance, ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ P A A B₀).symm⟩⟩


/-- A smooth algebra `B` with a section `s : B → A` over an integrally closed local domain `A`
descends, together with the section, to a smooth algebra `B₀` with a section `s₀` over a
Noetherian integrally closed local subring `P ⊆ A` containing a given finite set `E` and
dominated by `A`. -/
theorem exists_subring_smooth_model_section {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsIntegrallyClosed A] {E : Set A} (hE : E.Finite) (B : Type*) [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] (s : B →ₐ[A] A) :
    ∃ (P : Subring A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra P B₀) (s₀ : B₀ →ₐ[P] P)
      (e : B ≃ₐ[A] A ⊗[P] B₀), E ⊆ P ∧ IsNoetherianRing P ∧ IsLocalRing P ∧
      IsIntegrallyClosed P ∧ IsLocalHom P.subtype ∧ Algebra.Smooth P B₀ ∧
      ∀ b : B₀, s (e.symm (1 ⊗ₜ b)) = s₀ b := by
  obtain ⟨A₀, B₀, _, _, ⟨S, hS⟩, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg (R := ℤ) A B
  obtain ⟨T, hT⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A₀ B₀).FG)
  let f : B₀ →ₐ[A₀] A := (s.restrictScalars A₀).comp
    ((e.symm.toAlgHom.restrictScalars A₀).comp Algebra.TensorProduct.includeRight)
  obtain ⟨P, hEP, hnoeth, hloc, hint, hdom⟩ :=
    exists_subring_isNoetherianRing_isIntegrallyClosed
      ((hE.union S.finite_toSet).union (T.finite_toSet.image f))
  have hle : A₀ ≤ subalgebraOfSubring P := by
    rw [← hS, Algebra.adjoin_le_iff]
    exact fun x hx ↦ hEP (Or.inl (Or.inr hx))
  have hf (b : B₀) : f b ∈ P := by
    have hb : b ∈ Algebra.adjoin A₀ (T : Set B₀) := hT ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact hEP (Or.inr ⟨x, hx, rfl⟩)
    | algebraMap r => exact (f.commutes r).symm ▸ hle r.2
    | add x y _ _ hx hy => exact (map_add f x y).symm ▸ P.add_mem hx hy
    | mul x y _ _ hx hy => exact (map_mul f x y).symm ▸ P.mul_mem hx hy
  let : Algebra A₀ P := ((algebraMap A₀ A).codRestrict P fun x ↦ hle x.2).toAlgebra
  have : IsScalarTower A₀ P A := IsScalarTower.of_algebraMap_eq' rfl
  let f₀ : B₀ →ₐ[A₀] P :=
    { toRingHom := f.toRingHom.codRestrict P hf
      commutes' r := Subtype.ext (f.commutes r) }
  refine ⟨P, P ⊗[A₀] B₀, inferInstance, inferInstance,
    Algebra.TensorProduct.lift (Algebra.ofId P P) f₀ fun _ _ ↦ Commute.all _ _,
    e.trans (Algebra.TensorProduct.cancelBaseChange A₀ P A A B₀).symm,
    fun x hx ↦ hEP (Or.inl (Or.inl hx)), hnoeth, hloc, hint, hdom, inferInstance, fun b ↦ ?_⟩
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul p b =>
    simp only [AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
      Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.ofId_self,
      Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, Subring.coe_mul]
    rw [Subring.smul_def, ← TensorProduct.smul_tmul', map_smul,
      map_smul, smul_eq_mul]
    rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy, Subring.coe_add]

end IsLocalRing
