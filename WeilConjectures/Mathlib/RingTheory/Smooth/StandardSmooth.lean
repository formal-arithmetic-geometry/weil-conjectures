/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Standard smooth algebras over a regular ring are regular

Let `R` be a regular ring and let `S` be a standard smooth `R`-algebra, so that
`S = R[x₁, …, x_n] ⧸ (f₁, …, f_c)` for relations whose Jacobian matrix is invertible in `S`.
Then `S` is a regular ring.

The proof is the Jacobian criterion.  Fix a prime `𝔮` of `S` and let `Q` be its contraction to
`P := R[x₁, …, x_n]`.  Since `P` is a regular ring, `P_Q` is a regular local ring, and
`S_𝔮 = P_Q ⧸ (f₁, …, f_c)`; as the Jacobian is a unit its determinant is nonzero in the domain
`P ⧸ Q`, so `MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime` applies.

## Main results

* `Algebra.IsStandardSmooth.isRegularRing`: a standard smooth algebra over a regular ring is a
  regular ring.  In particular a standard smooth algebra over a field is a regular ring.
-/

@[expose] public section

open MvPolynomial

namespace Algebra

attribute [local instance] Fintype.ofFinite in
/-- **A standard smooth algebra over a regular ring is regular.**  In particular, a standard
smooth algebra over a field is a regular ring, so all its localisations at primes are regular
local rings. -/
theorem IsStandardSmooth.isRegularRing {R : Type*} [CommRing R] [IsRegularRing R]
    {S : Type*} [CommRing S] [Algebra R S] [IsStandardSmooth R S] : IsRegularRing S := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  have hsurj : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hquot : IsRegularRing (P.Ring ⧸ RingHom.ker (algebraMap P.Ring S)) := by
    refine IsRegularRing.quotient_of_forall_isRegularLocalRing _ ?_
    intro Q hQ hle
    have hle' : P.ker ≤ Q := hle
    have hrel : ∀ i, P.relation i ∈ Q := fun i ↦ hle' (P.relation_mem_ker i)
    have hmat : (Matrix.of fun j i ↦ pderiv (P.map j) (P.relation i)) = P.jacobiMatrix := by
      ext j i
      rw [P.jacobiMatrix_apply]
      rfl
    have hjac : (Matrix.of fun j i ↦ pderiv (P.map j) (P.relation i)).det ∉ Q := by
      intro hmem
      have h1 : P.jacobian ∈ Q.map (algebraMap P.Ring S) := by
        rw [P.jacobian_eq_jacobiMatrix_det, ← hmat]
        exact Ideal.mem_map_of_mem _ hmem
      have h2 : Q.map (algebraMap P.Ring S) ≠ ⊤ := by
        intro h
        have hc := Ideal.comap_map_of_surjective _ hsurj Q
        rw [h, Ideal.comap_top] at hc
        exact hQ.ne_top (hc.trans (sup_eq_left.mpr hle')).symm
      exact h2 (Ideal.eq_top_of_isUnit_mem _ h1 P.jacobian_isUnit)
    have := MvPolynomial.isRegularLocalRing_quotient_map_localization_atPrime
      (R := R) (ι := ι) (σ := σ) Q P.map P.relation hrel hjac
    rwa [P.span_range_relation_eq_ker] at this
  exact IsRegularRing.of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj)

end Algebra
