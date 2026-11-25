/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Unramified.Basic
import WeilConjectures.RingTheory.UniversalFirstOrderThickeningCore
import WeilConjectures.RingTheory.UniversalFirstOrderThickeningUniqueness

/-!
# Universal first order thickenings of formally unramified algebras

A formally unramified algebra admits a universal first order thickening, unique up to unique
isomorphism.

## Implementation details

Write `S = P/J` with `P` a polynomial algebra. The conormal map `J/J² → S ⊗[P] Ω[P/R]` is
surjective since `Ω[S/R] = 0`, and splits since the target is free. Taking `J'` to be the
preimage of the splitting, `S' = P/J'` is the universal thickening: lifts of `S → A/I` to `P`
differ by derivations, and exactly one of them kills `J'`. Uniqueness follows formally from the
universal property.

## References

* Stacks Project, Algebra, Lemma 04EB and the uniqueness remark in Section 04EA
-/

@[expose] public section

universe u

namespace Algebra

/-- A formally unramified algebra admits a universal square-zero thickening, unique up to
unique algebra isomorphism over the given algebra. -/
theorem exists_universalFirstOrderThickening
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [FormallyUnramified R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (π : S' →ₐ[R] S),
      Function.Surjective π ∧ RingHom.ker π.toRingHom ^ 2 = ⊥ ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
        ∀ a : S →ₐ[R] A ⧸ I,
          ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π) ∧
      (∀ (T : Type u) [CommRing T] [Algebra R T] (πT : T →ₐ[R] S),
        Function.Surjective πT → RingHom.ker πT.toRingHom ^ 2 = ⊥ →
        (∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A), I ^ 2 = ⊥ →
          ∀ a : S →ₐ[R] A ⧸ I,
            ∃! a' : T →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp πT) →
        ∃! e : S' ≃ₐ[R] T, πT.comp e.toAlgHom = π) := by
  obtain ⟨S', instCR, instAlg, π, hsurj, hker, hprop⟩ :=
    exists_universalFirstOrderThickening_core R S
  let : CommRing S' := instCR
  let : Algebra R S' := instAlg
  refine ⟨S', inferInstance, inferInstance, π, hsurj, hker, hprop, ?_⟩
  intro T _ _ πT hπT hkerT hT
  exact universalFirstOrderThickening_unique R S S' π hsurj hker hprop T πT hπT hkerT hT

end Algebra
