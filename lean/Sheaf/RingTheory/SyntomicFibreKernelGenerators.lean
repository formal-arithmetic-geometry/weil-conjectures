/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Sheaf.RingTheory.CompleteIntersectionOverField

/-!
# Fibre generators in a fixed polynomial presentation

Source: Stacks Project, Tag 00SY, proof of (3) implies (2); Tag 00SC.
(blueprint: lem-weil-pbc-syntomic-fibre-kernel-generators).
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Algebra

/-- Bounded equations generate the presentation kernel modulo the base prime in the
polynomial local ring. Source: Stacks Project, Tag 00SY, proof of (3) implies (2),
choice of equations; Tag 00SC, conormal rank.
(blueprint: lem-weil-pbc-syntomic-fibre-kernel-generators).

Proof: Put p = q ∩ R and Q = φ⁻¹(q). Base change the surjection to κ(p) and identify
κ(p) ⊗ P with κ(p)[x₁,…,xₙ], and its quotient with κ(p) ⊗ S. Transport the prime
corresponding to q and the given complete-intersection neighbourhood to this quotient.
The conormal rank theorem gives a basis with c = n - d ≤ n elements. The images of
I = ker φ generate the fibre ideal and therefore its conormal residue vector space.
The residue field at the fibre prime equals that at Q. In this vector space the
images of I are a spanning set, so select c of them forming a basis and take their
original representatives fᵢ ∈ I. Every coefficient denominator from κ(p) comes
from R ∖ p, hence is invertible in P_Q; every polynomial denominator lies outside
the inverse-image prime, hence is invertible in P_Q as well. Multiplying a chosen
basis vector by such a denominator preserves a basis. The polynomial fibre ring
is Noetherian; its localized ideal is therefore finite. Nakayama in that local
ring makes the fᵢ generate the fibre ideal. The fibre local ring is P_Q/pP_Q,
by the fibre-local-ring comparison.
Taking the inverse image of this equality says I P_Q ⊆ (fᵢ)P_Q + pP_Q.
This argument needs no flatness. For c = 0 the fibre ideal is zero and the same
containment holds with the zero ideal. The specified prime excludes a zero fibre. -/
theorem exists_bounded_fibre_kernel_generators
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) (n : ℕ) (φ : MvPolynomial (Fin n) R →ₐ[R] S)
    (hφ : Function.Surjective φ)
    (hci : ∃ h : (q.asIdeal.comap (algebraMap R S)).Fiber S,
      h ∉ (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩).asIdeal ∧
      IsGlobalCompleteIntersection (q.asIdeal.comap (algebraMap R S)).ResidueField
        (Localization.Away h)) :
    ∃ (c : ℕ) (f : Fin c → MvPolynomial (Fin n) R),
      c ≤ n ∧ Ideal.span (Set.range f) ≤ RingHom.ker φ.toRingHom ∧
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (RingHom.ker φ.toRingHom) ≤
      Ideal.map (algebraMap _
        (Localization.AtPrime (q.asIdeal.comap φ.toRingHom))) (Ideal.span (Set.range f)) ⊔
      Ideal.map (algebraMap R (Localization.AtPrime (q.asIdeal.comap φ.toRingHom)))
        (q.asIdeal.comap (algebraMap R S)) := by
  sorry

end Algebra
