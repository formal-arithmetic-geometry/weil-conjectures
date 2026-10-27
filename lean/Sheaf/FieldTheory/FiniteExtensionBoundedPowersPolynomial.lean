/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q60
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Bounded powers in a finite field extension

Source: the finite-extension norm argument assembled in the DAG from Mathlib's
spectral norm theorem and finite-dimensional continuity
(blueprint: lem-trf-finite-extension-bounded-powers-polynomial).
The node's BGR reference is descriptive: the book is not locally available and
no theorem number from it has been independently verified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

open scoped NNReal

namespace Polynomial

/-- Bounded powers for an arbitrary nonarchimedean vector-space norm give a monic
annihilating polynomial with coefficients of norm at most one.
Source: Mathlib, `Analysis/Normed/Unbundled/SpectralNorm.lean`, spectral norm theorem
and `spectralValue_le_one_iff`, assembled as the node's agent-written argument
(blueprint: lem-trf-finite-extension-bounded-powers-polynomial).

Proof:
1. Finite dimensionality makes L a finite F-module. By
   lem-weil-pbc-finite-algebra-is-integral, each element has a monic annihilator.
   Choose one of least degree. Its degree is positive because the monic constant
   polynomial 1 cannot vanish in a field. Two monic least-degree annihilators
   have lower-degree difference, so scaling a nonzero difference to be monic
   proves uniqueness. These are the minimal polynomials, without separability.
2. Apply lem-trf-spectral-norm-algebraic-extension: the spectral value of the
   minimal polynomial defines a multiplicative nonarchimedean norm s extending
   the given norm of F. The supplied vector-space norm ν need not be multiplicative.
3. The distances defined by ν and s make two Hausdorff topological F-vector
   spaces on L. The strong triangle inequality makes addition continuous, and
   N(cx-c₀x₀) ≤ max(‖c‖N(x-x₀), ‖c-c₀‖N(x₀)) proves scalar continuity.
   By lem-sfb-finite-dimensional-linear-map-continuous the identity from the
   ν-space to the s-space is continuous. Then
   lem-trf-continuous-linear-map-norm-bound gives C > 0 with s(x) ≤ Cν(x).
4. Choose M ≥ 1 bounding all ν(a^m). Multiplicativity yields
   s(a)^m = s(a^m) ≤ CM for every natural m, including zero. If s(a) > 1,
   set δ = s(a)-1 > 0. Induction gives (1+δ)^m ≥ 1+mδ; choosing
   m > (CM-1)/δ contradicts the uniform bound. Hence s(a) ≤ 1.
5. Take q to be the minimal polynomial of a. Its spectral value is s(a) ≤ 1,
   so lem-sfb-monic-spectral-value-coefficients bounds every coefficient by one.
   Monicity gives q = X^e + ∑ j < e, C(q.coeff j) * X^j for e = q.natDegree.
   Step 1 gives e ≥ 1 and aeval a q = 0, as required. -/
theorem exists_monic_of_finite_extension_bounded_powers
    (F : Type u) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (L : Type v) [Field L] [Algebra F L] [FiniteDimensional F L]
    (ν : L → ℝ≥0)
    (hν_zero : ∀ x : L, ν x = 0 ↔ x = 0)
    (hν_add : ∀ x y : L, ν (x + y) ≤ max (ν x) (ν y))
    (hν_smul : ∀ (c : F) (x : L), ν (c • x) = ‖c‖₊ * ν x)
    (a : L) (ha : ∃ M : ℝ≥0, ∀ m : ℕ, ν (a ^ m) ≤ M) :
    ∃ q : Polynomial F, q.Monic ∧ 1 ≤ q.natDegree ∧
      (∀ j : ℕ, j < q.natDegree → ‖q.coeff j‖ ≤ 1) ∧ aeval a q = 0 := by
  sorry

end Polynomial
