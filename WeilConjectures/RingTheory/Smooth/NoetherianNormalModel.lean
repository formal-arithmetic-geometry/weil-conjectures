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

end IsLocalRing
