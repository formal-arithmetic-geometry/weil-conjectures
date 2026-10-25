/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
import WeilConjectures.RingTheory.MvPolynomial.TwoVariableSyzygy
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The graded Koszul resolution on two polynomial variables

Source: literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-duality/
lem-sc-p1-graded-resolution.md, graded-resolution source note
(blueprint: lem-sc-p1-koszul-resolution).

`S = MvPolynomial (Fin 2) k` is graded by total degree through Mathlib's
`homogeneousSubmodule`, extended by zero in negative degrees, as in the landed
`MvPolynomial.exists_graded_free_resolution_two` (lem-sc-p1-graded-syzygy).
The underlying modules of `S(-2)` and `S(-1)` are `S`; by
`def-weil-pbc-proj-twisting-sheaf` (2), `S(d)_n = S_{d+n}`, so the degree `n + 2`
part of `S(-2)` is `S_n` and the degree `n + 1` part of `S(-1)` is `S_n`; all lower
parts are zero. The quotient `k = S/(x₀,x₁)` has the quotient grading, concentrated
in degree zero.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.ProjectiveLine

open MvPolynomial

/-- The exact graded Koszul resolution `0 → S(-2) → S(-1)² → S → S/(x₀,x₁) → 0`.
Source: the blueprint `lem-sc-p1-graded-resolution`, graded-resolution source note;
Stacks Algebra, Section 00JL, for the shift convention
(blueprint: lem-sc-p1-koszul-resolution).

The maps are `a ↦ (a x₁, -a x₀)`, `(a, b) ↦ a x₀ + b x₁` and the quotient map.
Degree zero: since negative-degree parts vanish, `f` sends `S(-2)_{n+2} = S_n` into
`S(-1)²_{n+2} = S_{n+1}²`, `g` sends `S(-1)²_{n+1} = S_n²` into `S_{n+1}`, and `q`
kills `S_{n+1}` (the quotient is concentrated in degree zero), for every `n : ℕ`.

Proof, following the node's four steps:
1. The shifts `M(d)_n = M_{d+n}` of `def-weil-pbc-proj-twisting-sheaf` make
   the two multiplication maps degree preserving. Commutativity gives their zero
   composite. The quotient kernel is `(x₀,x₁)`, the image of the second map.
2. `lem-weil-pbc-polynomial-ring-domain` says `S` is a domain. Since `x₀` is
   nonzero, `a*x₀ = 0` implies `a = 0`, giving injectivity of the first map.
3. `lem-sc-p1-linear-syzygy` gives `a = c*x₁` and `b = -c*x₀` whenever
   `a*x₀ + b*x₁ = 0`. Thus the middle kernel is the first image; the converse
   follows from step 1.
4. Assemble these kernel-image equalities and the surjective quotient map.
   Positive-degree monomials lie in `(x₀,x₁)`, so the quotient map is homogeneous
   into the quotient concentrated in degree zero. -/
theorem koszul_resolution {k : Type u} [Field k] :
    ∃ (f : MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k)
      (g : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k)
      (q : MvPolynomial (Fin 2) k →ₗ[MvPolynomial (Fin 2) k]
          MvPolynomial (Fin 2) k ⧸
            Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))),
      (∀ a : MvPolynomial (Fin 2) k, f a = (a * X 1, -a * X 0)) ∧
      (∀ p : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k,
        g p = p.1 * X 0 + p.2 * X 1) ∧
      (∀ a : MvPolynomial (Fin 2) k,
        q a = Ideal.Quotient.mk (Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))) a) ∧
      Function.Injective f ∧ Function.Exact f g ∧
      Function.Exact g q ∧ Function.Surjective q ∧
      (∀ a : MvPolynomial (Fin 2) k,
        q a = 0 ↔ a ∈ Ideal.span ({X 0, X 1} : Set (MvPolynomial (Fin 2) k))) ∧
      (∀ a : MvPolynomial (Fin 2) k, g (f a) = 0) ∧
      (∀ (n : ℕ) (a : MvPolynomial (Fin 2) k), a ∈ homogeneousSubmodule (Fin 2) k n →
        (f a).1 ∈ homogeneousSubmodule (Fin 2) k (n + 1) ∧
        (f a).2 ∈ homogeneousSubmodule (Fin 2) k (n + 1)) ∧
      (∀ (n : ℕ) (p : MvPolynomial (Fin 2) k × MvPolynomial (Fin 2) k),
        p.1 ∈ homogeneousSubmodule (Fin 2) k n → p.2 ∈ homogeneousSubmodule (Fin 2) k n →
        g p ∈ homogeneousSubmodule (Fin 2) k (n + 1)) ∧
      (∀ (n : ℕ) (a : MvPolynomial (Fin 2) k),
        a ∈ homogeneousSubmodule (Fin 2) k (n + 1) → q a = 0) := by
  let S := MvPolynomial (Fin 2) k
  let I : Ideal S := Ideal.span ({X 0, X 1} : Set S)
  let f : S →ₗ[S] S × S :=
    (LinearMap.mulRight S (X 1)).prod (-(LinearMap.mulRight S (X 0 : S)))
  let g : S × S →ₗ[S] S :=
    (LinearMap.mulRight S (X 0)).coprod (LinearMap.mulRight S (X 1))
  let q : S →ₗ[S] S ⧸ I := I.mkQ
  have hf (a : S) : f a = (a * X 1, -a * X 0) := by
    change (a * X 1, -(a * X 0)) = (a * X 1, -a * X 0)
    rw [neg_mul]
  have hg (p : S × S) : g p = p.1 * X 0 + p.2 * X 1 := rfl
  have hq (a : S) : q a = Ideal.Quotient.mk I a := rfl
  have hker (a : S) : q a = 0 ↔ a ∈ I := Ideal.Quotient.eq_zero_iff_mem
  have hcomp (a : S) : g (f a) = 0 := by
    rw [hg, hf]
    ring
  have hinj : Function.Injective f := by
    intro a b hab
    have h := congrArg Prod.fst hab
    rw [hf, hf] at h
    exact mul_right_cancel₀ (X_ne_zero (1 : Fin 2)) h
  have hfg : Function.Exact f g := by
    intro p
    constructor
    · intro hp
      obtain ⟨c, hc, hd⟩ := exists_eq_mul_X_and_eq_neg_mul_X p.1 p.2 ((hg p).symm.trans hp)
      exact ⟨c, by rw [hf]; exact Prod.ext hc.symm hd.symm⟩
    · rintro ⟨a, rfl⟩
      exact hcomp a
  have hgq : Function.Exact g q := by
    intro a
    rw [hker, Ideal.mem_span_pair]
    constructor
    · rintro ⟨b, c, hbc⟩
      exact ⟨(b, c), hbc⟩
    · rintro ⟨p, hp⟩
      exact ⟨p.1, p.2, (hg p).symm.trans hp⟩
  refine ⟨f, g, q, hf, hg, hq, hinj, hfg, hgq, I.mkQ_surjective,
    hker, hcomp, ?_, ?_, ?_⟩
  · intro n a ha
    rw [hf]
    exact ⟨ha.mul (isHomogeneous_X k 1), ha.neg.mul (isHomogeneous_X k 0)⟩
  · intro n p ha hb
    rw [hg]
    exact (ha.mul (isHomogeneous_X k 0)).add (hb.mul (isHomogeneous_X k 1))
  · intro n a ha
    apply (hker a).mpr
    have hrange : Set.range (X : Fin 2 → S) = ({X 0, X 1} : Set S) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    change a ∈ Ideal.span ({X 0, X 1} : Set S)
    rw [← hrange]
    change a ∈ idealOfVars (Fin 2) k
    rw [← pow_one (idealOfVars (Fin 2) k), mem_pow_idealOfVars_iff]
    intro d hd
    have hdeg : d.degree = n + 1 := by
      rw [Finsupp.degree_eq_weight_one]
      exact ha (mem_support_iff.mp hd)
    omega

end AlgebraicGeometry.ProjectiveLine
