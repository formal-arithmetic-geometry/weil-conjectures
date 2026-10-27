/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import Mathlib.Dynamics.Newton

/-!
# Unique lifting of coprime monic factorizations modulo locally nilpotent ideals

Source: Stacks Project, More on Algebra, Tag 0ALI, final factorization paragraph
(blueprint: lem-weil-pbc-henselian-factorization-locally-nilpotent).
Existence is the Stacks assertion; uniqueness is the agent-written argument of the DAG node.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A coprime monic factorization modulo an ideal whose elements are nilpotent lifts uniquely.
Source: Stacks Project, Tag 0ALI, final paragraph, for existence; the DAG's agent-written
uniqueness argument (blueprint: lem-weil-pbc-henselian-factorization-locally-nilpotent).

Proof:
1. The ideal `J` lies in the Jacobson radical: for `x ∈ J`, every `x*y` is nilpotent,
   so `1 + x*y` is a unit. Consequently reduction modulo `J` reflects units.
2. For a simple approximate root `x` of a polynomial `P`, finite Newton iteration
   terminates because `P(x)` is nilpotent. Mathlib's Newton error-divisibility lemma
   gives a root after sufficiently many iterations. Inductively every iterate is
   congruent to `x` modulo `J`, since each correction is a multiple of `P` at the
   preceding iterate. Thus `(A,J)` satisfies Mathlib's simple-root definition of henselian.
3. Apply `henselianRing_iff_factorization_criterion` to obtain the monic factors.
4. Lift Bezout coefficients for `g₀,h₀`. For any lifts `g,h'`, the polynomial
   `a*g + b*h' - 1` has coefficients in `J`, hence is nilpotent. Thus `a*g + b*h'`
   is a unit; multiplying by its inverse gives a Bezout identity for `g,h'`.
5. Given two lifts `f = g*h = g'*h'`, coprimality of `g,h'` shows `g ∣ g'`.
   In the zero ring uniqueness is immediate. Otherwise `J` is proper, and reduction
   preserves monic degrees. The monic divisibility and equal-degree lemma gives
   `g' = g`; cancel the regular monic polynomial `g` to conclude `h' = h`.
-/
theorem existsUnique_monic_factorization_of_locally_nilpotent
    {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : ∀ x : A, x ∈ J → IsNilpotent x)
    (f : A[X]) (hf : f.Monic) (g₀ h₀ : (A ⧸ J)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcoprime : IsCoprime g₀ h₀)
    (hfactor : f.map (Ideal.Quotient.mk J) = g₀ * h₀) :
    ∃! gh : A[X] × A[X],
      gh.1.Monic ∧ gh.2.Monic ∧ f = gh.1 * gh.2 ∧
        gh.1.map (Ideal.Quotient.mk J) = g₀ ∧ gh.2.map (Ideal.Quotient.mk J) = h₀ := by
  classical
  have hjac : J ≤ Ideal.jacobson (⊥ : Ideal A) := by
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    exact (hJ _ (J.mul_mem_right y hx)).isUnit_add_one
  let : IsLocalHom (Ideal.Quotient.mk J) := isLocalHom_of_le_jacobson_bot J hjac
  have henselian : HenselianRing A J := by
    refine ⟨hjac, ?_⟩
    intro P _ x hx hderiv
    have hunit : IsUnit (aeval x P.derivative) := by
      simpa using isUnit_of_map_unit (Ideal.Quotient.mk J) _ hderiv
    have hn : IsNilpotent (aeval x P) := by
      simpa using hJ _ hx
    obtain ⟨n, hnzero⟩ := hn
    have hroot : aeval (P.newtonMap^[n] x) P = 0 := by
      rw [← zero_dvd_iff, ← pow_eq_zero_of_le (n.lt_two_pow_self).le hnzero]
      exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap ⟨n, hnzero⟩ hunit n
    have hmod : ∀ k : ℕ, P.newtonMap^[k] x - x ∈ J := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have heval : P.eval (P.newtonMap^[k] x) ∈ J := by
          have hd := J.mem_of_dvd (sub_dvd_eval_sub (P.newtonMap^[k] x) x P) ih
          exact (J.sub_mem_iff_left hx).mp hd
        rw [Function.iterate_succ_apply', newtonMap_apply, sub_right_comm]
        exact J.sub_mem ih (J.mul_mem_left _ (by simpa using heval))
    exact ⟨P.newtonMap^[n] x, by simpa [IsRoot] using hroot, hmod n⟩
  obtain ⟨g, h, hg, hh, hfac, hgm, hhm⟩ :=
    ((henselianRing_iff_factorization_criterion A J).1.mp henselian).2
      f hf g₀ h₀ hg₀ hh₀ hcoprime hfactor
  refine ⟨(g, h), ⟨hg, hh, hfac, hgm, hhm⟩, ?_⟩
  rintro ⟨g', h'⟩ ⟨hg', hh', hfac', hgm', hhm'⟩
  have hc : IsCoprime g h' := by
    obtain ⟨a₀, b₀, hab₀⟩ := hcoprime
    obtain ⟨a, rfl⟩ := map_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective a₀
    obtain ⟨b, rfl⟩ := map_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective b₀
    have hmap : (a * g + b * h' - 1).map (Ideal.Quotient.mk J) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_one, hgm, hhm', hab₀, sub_self]
    have hnilpoly : IsNilpotent (a * g + b * h' - 1) := by
      rw [Polynomial.isNilpotent_iff]
      intro i
      apply hJ
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [coeff_map, coeff_zero] using congrArg (fun p ↦ p.coeff i) hmap
    have hu : IsUnit (a * g + b * h') := by
      simpa only [sub_add_cancel] using hnilpoly.isUnit_add_one
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mp hu
    refine ⟨c * a, c * b, ?_⟩
    simpa only [mul_add, mul_assoc] using hc
  nontriviality A
  have hJtop : J ≠ ⊤ := by
    intro ht
    exact not_isNilpotent_one (hJ 1 (by rw [ht]; trivial))
  let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  have hdvd : g ∣ g' := hc.dvd_of_dvd_mul_right (hfac' ▸ hfac ▸ dvd_mul_right g h)
  have hgg : g' = g := eq_of_monic_of_dvd_of_natDegree_le hg hg' hdvd (by
    rw [← hg'.natDegree_map (Ideal.Quotient.mk J), hgm',
      ← hgm, hg.natDegree_map])
  have hhh : h' = h := hg.isRegular.left (by
    change g * h' = g * h
    calc
      g * h' = g' * h' := by rw [hgg]
      _ = f := hfac'.symm
      _ = g * h := hfac)
  exact Prod.ext hgg hhh

end Polynomial
