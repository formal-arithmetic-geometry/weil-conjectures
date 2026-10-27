/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q76
-/
module

public import Sheaf.RingTheory.CoordinateQuotientGrading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.GroupTheory.MonoidLocalization.Away

/-! # Degree bounds and emptiness for coordinate Hilbert polynomials

Source: Stacks Project, varieties.tex, Tag 08AC and the monomial count following
Definition 08AD; constructions.tex, standard Proj charts. The growth and nilpotence
argument is the agent-written proof recorded in the node.
(blueprint: lem-sfb-graded-coordinate-polynomial-degree-emptiness)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- An eventual coordinate dimension polynomial is bounded by the monomial count;
when nonzero it has positive leading coefficient and degree at most n. Its vanishing
is equivalent both to a zero graded tail and to emptiness of the actual quotient Proj.
This includes the unit ideal, without reducedness or saturation hypotheses.

Source: Stacks Project, varieties.tex, Tag 08AC and the subsequent degree-d monomial
count; constructions.tex, standard Proj charts; algebra.tex, Tag 00E0.
(blueprint: lem-sfb-graded-coordinate-polynomial-degree-emptiness)

Proof (the node's six steps):
1. The degree-d monomials of B are a basis, indexed by n+1 nonnegative exponents
summing to d (def-weil-pbc-mv-polynomial-ring). Stars and bars counts them as
choose (d+n) n, including n=0 and d=0. Their quotient images span A_d by
def-sfb-coordinate-quotient-grading. Extracting a basis bounds its finite dimension
(def-weil-vector-space-dimension), and hQ gives the two numerical inequalities.
2. If Q is nonzero, put r=natDegree Q and a=leadingCoeff Q. Apply
lem-sfb-polynomial-leading-term-asymptotic with epsilon=1/2. For large positive d,
abs (Q(d)-a*d^r) is at most abs a*d^r/2. A negative a contradicts nonnegative Q(d),
so a>0 and Q(d) is at least a*d^r/2 eventually. If r>n, the monomial bound and
choose (d+n) n <= (d+n)^n <= (n+1)^n*d^n give a*d/2 <= (n+1)^n for arbitrarily
large integers d, a contradiction. Thus r<=n (def-weil-polynomial-ring).
3. Q=0 forces dimension zero, hence A_d=0, for d>=d0. Conversely a vanishing tail
makes Q(d)=0 eventually, contradicting step 2 if Q is nonzero.
4. The images u_i of the variables generate A_+: positive-degree monomials contain
a variable, and their images span the pieces (def-sfb-coordinate-quotient-grading,
def-weil-pbc-mv-polynomial-ring). A vanishing tail makes every u_i nilpotent, so
every prime contains A_+ and Proj has no points (def-pc-proj).
5. If Proj is empty, each standard chart Spec A_(u_i) is empty (def-pc-proj).
The radical of zero is the intersection of the primes
(lem-weil-pbc-zero-locus-eq-iff-radical-eq); hence it contains 1 and the chart ring
has 1=0. Degree-zero homogeneous localization embeds in A[1/u_i]
(def-nagata-homogeneous-localization-degree-zero). The fraction relation then gives
u_i^k_i=0 (def-weil-ring-localization-away). Replace k_i by e_i=max(1,k_i).
6. Set D=1+sum (e_i-1). Every degree-d monomial with d>=D has some exponent at
least e_i, so its quotient image is zero. These images span A_d, hence the tail
vanishes. Steps 3--5 give all three equivalences, including the zero quotient. -/
theorem coordinateQuotient_polynomial_degree_emptiness
    {k : Type u} [Field k] (n : ℕ)
    (J : @HomogeneousIdeal _ _ _ _ _ _
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k)
      _ _ MvPolynomial.gradedAlgebra)
    (Q : Polynomial ℚ) (d₀ : ℕ)
    (hQ : ∀ d : ℕ, d₀ ≤ d →
      Q.eval (d : ℚ) = (Module.finrank k (coordinateQuotientPiece J d) : ℚ)) :
    (∀ d : ℕ, d₀ ≤ d →
      0 ≤ Q.eval (d : ℚ) ∧ Q.eval (d : ℚ) ≤ (Nat.choose (d + n) n : ℚ)) ∧
    (Q ≠ 0 → 0 < Q.leadingCoeff ∧ Q.natDegree ≤ n) ∧
    (Q = 0 ↔ ∃ D : ℕ, ∀ d : ℕ, D ≤ d → coordinateQuotientPiece J d = ⊥) ∧
    ((∃ D : ℕ, ∀ d : ℕ, D ≤ d → coordinateQuotientPiece J d = ⊥) ↔
      IsEmpty (Proj (coordinateQuotientPiece J))) := by
  sorry

end AlgebraicGeometry
