/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
public import Mathlib.Algebra.Polynomial.Basic
import WeilConjectures.RingTheory.MonogenicNagataDomainN2
import WeilConjectures.RingTheory.FiniteOverNagata

/-!
# Polynomial rings over Nagata rings

A polynomial ring in one variable over a Nagata ring is Nagata.

## Implementation details

For a prime `q` of `R[X]` over `p`, the domain `R[X] / q` is generated over `R / p` by one
element. If it is transcendental the quotient is a polynomial ring, which is N-2 (Tag 032O).
Otherwise, for a finite extension `M` of the fraction field, the integral closure `A'` of `R / p`
in `M` is finite and `A'[x]` is N-1 by claim (***) of Tag 0334.

## References

* [Stacks, Tag 0334] (steps 2–4)
* [Stacks, Tag 032O]
-/

@[expose] public section

universe u

/-- A polynomial ring in one variable over a Nagata ring is Nagata. -/
theorem isNagataRing_polynomial (R : Type u) [CommRing R]
    (hR : IsNagataRing R) : IsNagataRing (Polynomial R) := by
  let : IsNoetherianRing R := hR.1
  refine ⟨inferInstance, ?_⟩
  intro q hq
  let p : Ideal R := q.comap (algebraMap R (Polynomial R))
  have hp : p.IsPrime := Ideal.IsPrime.comap (algebraMap R (Polynomial R))
  let : p.IsPrime := hp
  have hA : IsNagataRing (R ⧸ p) :=
    (finite_over_nagata_is_nagata R R hR).2 p
  let x : Polynomial R ⧸ q := Ideal.Quotient.mk q Polynomial.X
  apply isN2_of_monogenic_nagata_domain (R ⧸ p) (Polynomial R ⧸ q) hA
    Ideal.algebraMap_quotient_injective x
  apply eq_top_iff.mpr
  intro b hb
  clear hb
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction f using Polynomial.induction_on' with
  | add f g hf hg =>
      exact (Algebra.adjoin (R ⧸ p) ({x} : Set (Polynomial R ⧸ q))).add_mem hf hg
  | monomial n r =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      apply Subalgebra.mul_mem
      · exact (Algebra.adjoin (R ⧸ p) ({x} : Set (Polynomial R ⧸ q))).algebraMap_mem
          (Ideal.Quotient.mk p r)
      · exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton x)) n

