/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.RingTheory.GabberIntegralSectionFactor
import WeilConjectures.RingTheory.ZariskiPairFlatIntegralIsomorphism

/-!
# Étale section lifting from Gabber's root condition

If an ideal `I` in the Jacobson radical of `A` satisfies Gabber's root condition, then every
`A`-algebra section `B → A/I` of an étale `A`-algebra `B` lifts to a section `B → A`.

## Implementation details

The section modulo `I` gives an idempotent `ε` of `B/IB` splitting off `A/I`. Passing to a finite
subalgebra of the integral closure of `A` in `B`, one finds an element `b` lifting `ε` that is
annihilated by a polynomial `f = Xⁿ(X - 1) + ∑ aⱼ Xʲ` with `aⱼ ∈ I`. A root `α` of `f` with
`α - 1 ∈ I` is a unit, and writing `f = (X - α)g` the polynomial `E = g(α)⁻¹ g` gives an
idempotent `e = E(b)` lifting `ε` with `be = αe`. Then `A → B_e` is étale, flat, integral and an
isomorphism modulo `I`, hence an isomorphism, and `B → B_e ≅ A` is the required lift.

## References

* [Stacks, Tag 09XI], implication (5) ⇒ (2)
-/

@[expose] public section

universe u v

open Polynomial
open scoped BigOperators

namespace Algebra

/-- Gabber's root condition for an ideal in the Jacobson radical implies that every
section of an étale algebra modulo that ideal lifts to an algebra section. -/
theorem exists_etale_section_lift_of_gabber_roots
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    (hroots : ∀ (n : ℕ), 1 ≤ n → ∀ (a : Fin (n + 1) → A),
      (∀ j, a j ∈ I) → ∀ (f : A[X]), f.Monic →
        f = X ^ n * (X - 1) + ∑ j : Fin (n + 1), C (a j) * X ^ (j : ℕ) →
          ∃ α : A, α - 1 ∈ I ∧ f.IsRoot α)
    (B : Type v) [CommRing B] [Algebra A B] [Etale A B] (σ : B →ₐ[A] A ⧸ I) :
    ∃ τ : B →ₐ[A] A, (Ideal.Quotient.mkₐ A I).comp τ = σ := by
  classical
  obtain ⟨e, _he, hint, hquot, ρ, hρ⟩ :=
    exists_gabber_integral_section_factor A I hI hroots B σ
  have hbij : Function.Bijective (algebraMap A (Localization.Away e)) :=
    RingHom.zariskiPair_flat_integral_finitePresentation_isIso
      (algebraMap A (Localization.Away e)) I (by simpa only [Ideal.jacobson_bot] using hI)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) hint
      (RingHom.finitePresentation_algebraMap.mpr inferInstance) hquot
  let Φ : A ≃ₐ[A] Localization.Away e := AlgEquiv.ofBijective (Algebra.ofId A _) hbij
  let τ : B →ₐ[A] A := Φ.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B _)
  refine ⟨τ, ?_⟩
  apply AlgHom.ext
  intro x
  change Ideal.Quotient.mkₐ A I (Φ.symm (algebraMap B (Localization.Away e) x)) = σ x
  rw [← hρ x]
  calc
    _ = ρ (algebraMap A (Localization.Away e)
        (Φ.symm (algebraMap B (Localization.Away e) x))) := (ρ.commutes _).symm
    _ = ρ (algebraMap B (Localization.Away e) x) :=
      congrArg ρ (Φ.apply_symm_apply _)

end Algebra
