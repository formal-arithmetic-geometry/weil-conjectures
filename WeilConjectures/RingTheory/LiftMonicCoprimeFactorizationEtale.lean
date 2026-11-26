/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Coprime.Basic
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting
import WeilConjectures.RingTheory.LiftMonicCoprimeFactorizationEtaleCore

/-!
# Lifting monic coprime factorizations after an étale extension

A factorization of a monic polynomial modulo `I` into monic coprime factors lifts after an étale
extension `A → A'` with `A/I ≃ A'/IA'`.

## Implementation details

The universal coprime factorization ring `B`, already localized at the resultant (replacing the
localization of Stacks 07M0), is étale over `A`. Its universal property gives a section of the
étale `A/I`-algebra `B/IB`, which splits off an idempotent `e`. Lifting `e` to `b ∈ B` and
taking `A' = B_b` gives an étale algebra with `A'/IA' ≃ (B/IB)_e ≃ A/I`, and the universal
factors map to the required lifts.

## References

* [Stacks, Tag 0ALH]
* [Stacks, Tag 07M0]
-/

@[expose] public section

universe u

namespace Polynomial

/-- A monic coprime factorization modulo an ideal lifts after an étale ring extension
whose canonical map on quotients is an isomorphism. -/
theorem exists_etale_lift_monic_coprime_factorization
    {A : Type u} [CommRing A] (I : Ideal A) (f : A[X]) (hf : f.Monic)
    (g₀ h₀ : (A ⧸ I)[X]) (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hfactor : f.map (Ideal.Quotient.mk I) = g₀ * h₀) (hcoprime : IsCoprime g₀ h₀) :
    ∃ (A' : Type u) (_ : CommRing A') (φ : A →+* A'),
      let J : Ideal A' := I.map φ
      let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧
        Function.Bijective α ∧
        ∃ g' h' : A'[X], g'.Monic ∧ h'.Monic ∧ f.map φ = g' * h' ∧
          g'.map (Ideal.Quotient.mk J) = g₀.map α ∧
          h'.map (Ideal.Quotient.mk J) = h₀.map α := by
  obtain ⟨A', _, φ, hE, hbij, g', h', hg', hh', hfac, hgred⟩ :=
    exists_etale_lift_monic_coprime_factorization_core I f hf g₀ h₀ hg₀ hh₀
      hfactor hcoprime
  let J : Ideal A' := I.map φ
  let α : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J φ Ideal.le_comap_map
  have hhred := lift_monic_coprime_factorization_h_reduction I f g₀ h₀ hg₀ hh₀ hfactor
    A' φ g' h' hfac hgred
  exact ⟨A', inferInstance, φ, hE, hbij, g', h', hg', hh', hfac, hgred, hhred⟩

end Polynomial
