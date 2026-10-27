/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q52
-/
module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Algebra.Polynomial.Eval.Defs
import WeilConjectures.Mathlib.Algebra.Group.ForwardDiff
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial lifting through injective graded multiplication

Source: Stacks Project, Algebra, Tags 00K1 and 00JZ
(blueprint: lem-trf-graded-injective-multiplication-polynomial-lift).
-/

@[expose] public section

set_option autoImplicit false

open scoped Pointwise

namespace GradedAlgebra

universe u v w

/-- The quotient by an injective degree-one multiplier has the quotient grading, the shifted
short exact sequences, and the associated dimension recurrence. An eventual rational polynomial
for the quotient dimensions integrates to one for the original dimensions.

Source: Stacks Project, Algebra, Tag 00K1, final paragraph of
`proposition-graded-hilbert-polynomial`, and Tag 00JZ, `lemma-numerical-polynomial`
(blueprint: lem-trf-graded-injective-multiplication-polynomial-lift).

Proof:
1. Compare the finite homogeneous decompositions of `m` and `x • m`. This proves that `xN`
   is homogeneous, has zero degree-zero part, and intersects degree `n + 1` in `xNₙ`.
   The images of the pieces therefore span the quotient independently, giving its grading.
   The canonical multiplication and quotient maps give the displayed short exact sequences.
2. Identify `Nₙ` with `xNₙ` by injectivity, and the quotient of `Nₙ₊₁` by that image with
   `Cₙ₊₁`. Apply `lem-trf-vector-space-quotient-dimension` to obtain finiteness and the
   rational dimension recurrence.
3. For an eventual formula starting at `d`, set `f(t) = dim N_(d+t)` and
   `A(X) = P(X+d+1)`. The recurrence gives `f(t+1)-f(t) = A(t)`. Apply
   `lem-trf-rational-sequence-polynomial-forward-difference` with `b = A.natDegree + 1`
   (also when `A = 0`), then translate the resulting polynomial by `-d`. Take `c = 0`
   and `e = d` to obtain the eventual dimension formula.
4. At every natural `n ≥ d+1`, the formula gives `B(n)-B(n-1) = P(n)`. These are
   infinitely many distinct rationals, so `lem-trf-polynomial-infinite-evaluation-identity`
   gives the polynomial identity. Zero polynomials and the zero module require no exclusion.
-/
theorem injective_multiplication_polynomial_lift
    {k : Type u} {S : Type v} {N : Type w}
    [Field k] [CommRing S] [Algebra k S] [AddCommGroup N]
    [Module k N] [Module S N] [IsScalarTower k S N]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] [IsStandard 𝒜]
    (𝒩 : ℕ → Submodule k N) [DirectSum.Decomposition 𝒩]
    [SetLike.GradedSMul 𝒜 𝒩] [∀ n : ℕ, FiniteDimensional k (𝒩 n)]
    (x : S) (hx : x ∈ 𝒜 1)
    (hinj : Function.Injective (fun m : N ↦ x • m)) :
    DirectSum.IsInternal (fun n : ℕ ↦
      (𝒩 n).map ((x • (⊤ : Submodule S N)).mkQ.restrictScalars k)) ∧
    (∀ n : ℕ, FiniteDimensional k
      ((𝒩 n).map ((x • (⊤ : Submodule S N)).mkQ.restrictScalars k))) ∧
    (∀ n : ℕ,
      ∃ μ : 𝒩 n →ₗ[k] 𝒩 (n + 1),
      ∃ q : 𝒩 (n + 1) →ₗ[k]
        ((𝒩 (n + 1)).map ((x • (⊤ : Submodule S N)).mkQ.restrictScalars k)),
        (∀ m : 𝒩 n, (μ m : N) = x • (m : N)) ∧
        (∀ m : 𝒩 (n + 1), (q m : QuotSMulTop x N) = Submodule.Quotient.mk (m : N)) ∧
        Function.Injective μ ∧ Function.Exact μ q ∧ Function.Surjective q ∧
        (Module.finrank k (𝒩 (n + 1)) : ℚ) - (Module.finrank k (𝒩 n) : ℚ) =
          (Module.finrank k
            ((𝒩 (n + 1)).map ((x • (⊤ : Submodule S N)).mkQ.restrictScalars k)) : ℚ)) ∧
    (∀ (P : Polynomial ℚ) (d : ℕ),
      (∀ n : ℕ, d ≤ n → (Module.finrank k
        ((𝒩 n).map ((x • (⊤ : Submodule S N)).mkQ.restrictScalars k)) : ℚ) =
          P.eval (n : ℚ)) →
      ∃ (B : Polynomial ℚ) (c : ℚ) (e : ℕ),
        B - B.comp (Polynomial.X - Polynomial.C 1) = P ∧
        ∀ n : ℕ, e ≤ n → (Module.finrank k (𝒩 n) : ℚ) = B.eval (n : ℚ) + c) := by
  sorry

end GradedAlgebra
