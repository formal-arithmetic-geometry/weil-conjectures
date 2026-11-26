/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Localization.Away.Basic

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.Free

/-!
# Finite projective modules are free on a neighbourhood of each prime

A finite projective module becomes finite free after inverting an element outside any given
prime.

## Main results

* `Module.exists_localizationAway_equiv_finsupp_of_finite_projective`

## Implementation details

A finite projective module is finitely presented, and its localization at `p` is finite free
over the local ring. Clearing the denominators of a basis gives a map from a finite free module
that is an isomorphism at `p`, and finite presentation spreads it to some `Away f` with
`f ∉ p`.

## References

* [Stacks, Tag 00NX] ((2) ⇒ (3) ⇒ (1) ⇒ (7))
* [Stacks, Tag 0GWM]
-/

@[expose] public section

universe u v

namespace Module

/-- A finite projective module becomes finite free after inverting an element outside any
specified prime `p`: there are `f ∉ p` and `r` with `M_f ≃ (A_f)^r`. -/
theorem exists_localizationAway_equiv_finsupp_of_finite_projective
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Projective A M] (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∃ r : ℕ,
      Nonempty (LocalizedModule.Away f M ≃ₗ[Localization.Away f]
        (Fin r →₀ Localization.Away f)) := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_projective A M
  have : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
  obtain ⟨f, hf, b', _⟩ :=
    Module.FinitePresentation.exists_basis_localizedModule_powers p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p) b
  exact ⟨f, hf, _, ⟨b'.repr⟩⟩

end Module
