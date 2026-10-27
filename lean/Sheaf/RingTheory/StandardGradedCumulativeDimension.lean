module

public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.RingTheory.KrullDimension.Basic

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.Roots
import Sheaf.RingTheory.HilbertSamuelGrowthDimension

/-!
# Dimension from the cumulative Hilbert polynomial

Source: Stacks Project, Algebra, Tag 00P6, `lemma-dimension-graded`, part (3),
in cumulative form, including the case of eventually zero graded pieces
(blueprint: lem-sfb-standard-graded-cumulative-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace GradedAlgebra.IsStandard

/-- The degree of the nonzero cumulative Hilbert polynomial is the finite Krull dimension.
If the graded pieces eventually vanish, the polynomial is a positive constant and the
Krull dimension is zero. Nontriviality makes the degree-zero image of the field a copy of
that field, as required by `S₀ = k`.

Source: Stacks Project, Algebra, Tag 00P6, `lemma-dimension-graded`, part (3),
in cumulative form (blueprint: lem-sfb-standard-graded-cumulative-dimension).

Proof plan:
1. Let `m = S₊` and `R = S_m`. By `lem-sfb-standard-graded-vertex-dimension`, `m` is
   maximal and `dim S = dim R`. The constant-component map gives `S/m = k`, hence the
   residue field of `R` is `k` and its maximal ideal is `n = mR`.
2. A field is Noetherian. Finite generation and
   `lem-weil-pbc-finite-type-algebra-noetherian` make `S` Noetherian; then
   `lem-weil-pbc-localization-noetherian` makes `R` Noetherian.
3. By `def-pc-standard-graded-algebra`, degree-`d` elements are linear combinations of
   degree-`d` monomials in degree-one generators. Thus `m^j` is the sum of the pieces
   of degrees at least `j`, and `m^j/m^(j+1)` identifies with the degree-`j` piece.
4. Localization gives a linear isomorphism from that piece to `n^j/n^(j+1)`.
   A fraction `b/u` has class `b_j/u₀`, because `u₀` is nonzero and higher components
   vanish in this quotient. If `a/1` vanishes, clearing denominators gives `wa` in
   `m^(j+1)` with `w₀` nonzero; its degree-`j` component is `w₀a`, so `a = 0`.
5. Apply `lem-trf-maximal-adic-graded-length-bridge`: the length of `R/n^n` is the
   cumulative sum in the hypothesis. By `lem-trf-hilbert-samuel-growth-dimension`, it
   eventually equals a nonzero polynomial of degree `dim R`.
6. By `lem-trf-polynomial-infinite-evaluation-identity`, that polynomial equals `Q`,
   since their values agree at infinitely many natural numbers in the rationals.
   Consequently `dim S = dim R = deg Q`. If the pieces vanish from degree `D` on,
   the cumulative sum is eventually the constant sum over degrees less than `D`.
   This sum is at least `dim S₀ = 1`. The same polynomial identity makes `Q` this
   positive constant, and the dimension equality gives dimension zero.
-/
theorem ringKrullDim_eq_natDegree_cumulative
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Nontrivial S] [Algebra k S]
    (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜] [IsStandard 𝒜]
    (Q : Polynomial ℚ) (hQ : Q ≠ 0) (N : ℕ) (hN : 1 ≤ N)
    (hpoly : ∀ n : ℕ, N ≤ n →
      Q.eval (n : ℚ) = ∑ j ∈ Finset.range n, (Module.finrank k (𝒜 j) : ℚ)) :
    ringKrullDim S = (Q.natDegree : WithBot ℕ∞) ∧
      ((∃ D : ℕ, ∀ j : ℕ, D ≤ j → 𝒜 j = ⊥) →
        ∃ c : ℚ, 0 < c ∧ Q = Polynomial.C c ∧ ringKrullDim S = 0) := by
  sorry

end GradedAlgebra.IsStandard
