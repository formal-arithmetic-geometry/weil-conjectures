/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.HenselianLocalRootLifting

/-!
# Stability of a simple root over a henselian valued field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé XX, section 4.4,
printed page 374, the root-perturbation form of Krasner used in Bourbaki,
Commutative Algebra, VI, section 8, exercises 12 and 14(a); Stacks Project,
Algebra, Tag 04GG supplies simple-root lifting
(blueprint: lem-per-henselian-simple-root-stability).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Valued

/-- A simple root of a monic polynomial over a nontrivially valued henselian field
persists in any prescribed open neighbourhood after sufficiently small perturbations
of the nonleading coefficients. The coefficient space has its product topology.
The ordered value group has arbitrary rank; no completeness hypothesis is used.

Source: ILO, Travaux de Gabber, Exposé XX, section 4.4, printed page 374,
Bourbaki VI, section 8, exercises 12 and 14(a), with Stacks Project, Algebra,
Tag 04GG as the root-lifting input
(blueprint: lem-per-henselian-simple-root-stability).

Proof (the seven steps of the node, in additive valuation notation):
1. If the topology is discrete, take the singleton coefficient neighbourhood and b = a.
   Otherwise every ball about zero contains a nonzero element of arbitrarily high value.
   The valuation ring R and its positive-value ideal m form the assumed henselian local
   ring (def-trf-valuation-ring and def-weil-pbc-henselian-terminology).
2. Choose a ball of radius bound gamma about a contained in U. Expand
   f(a + Z) = sum A_j Z^j by the binomial formula (def-weil-polynomial-ring).
   Then A_0 = 0 and A_1 = e = f'(a) is nonzero. Choose nonzero t, with value delta,
   such that delta > max(0, gamma) and delta > v(e) - v(A_j) for every nonzero
   A_j with j at least two. Finiteness suffices, without a rank-one assumption.
3. For the perturbed coefficients d, write g(a + Z) = sum B_j(d) Z^j. Set
   theta_j = v(e) - (j - 1) delta. A finite common bound on the coefficient
   differences ensures v(B_j(d) - A_j) > theta_j for every j. The product of
   the corresponding coefficient balls is the required open neighbourhood V of c.
4. For d in V, h(X) = g(a + tX)/(te) has coefficients h_j = B_j(d)t^(j-1)/e
   in R. Its constant term lies in m, its linear coefficient is one modulo m,
   and its higher coefficients lie in m. Thus its reduction is X, and its degree is n.
5. Make h monic by taking Q(Y) = h(1)^(-1) sum h_j Y^(n-j)(Y+1)^j.
   The element h(1) is a unit; the leading coefficient of Q is one and its
   reduction is Y^(n-1)(Y+1). Hence -1 is a simple residue root, also for n = 1
   and in residue characteristic two.
6. Apply lem-weil-pbc-henselian-local-root-lifting to Q and the residue root -1.
   The lift y is a unit. Then z = 1 + y^(-1) belongs to m, and
   Q(y) = h(1)^(-1)y^n h(z) = 0 implies h(z) = 0.
7. Set b = a + tz. Then g(b) = 0 and v(b-a) > gamma, so b belongs to U.
   Reduction of h'(z) is one. Differentiating the polynomial identity for h gives
   g'(b) = e h'(z), which is nonzero. Thus b is simple. All bounds are finite
   ordered-group comparisons, with no completeness or rank restriction. -/
theorem exists_open_coefficients_simple_root
    (F : Type u) [Field F] (Γ₀ : Type v) [LinearOrderedCommGroupWithZero Γ₀]
    [vF : Valued F Γ₀] [vF.v.IsNontrivial] [HenselianLocalRing vF.v.integer]
    (n : ℕ) (hn : 1 ≤ n) (c : Fin n → F) (a : F)
    (ha : (Polynomial.X ^ n +
      ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).eval a = 0)
    (hda : (Polynomial.X ^ n +
      ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)).derivative.eval a ≠ 0)
    (U : Set F) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ V : Set (Fin n → F), IsOpen V ∧ c ∈ V ∧
      ∀ d ∈ V, ∃ b ∈ U,
        (Polynomial.X ^ n +
          ∑ i : Fin n, Polynomial.C (d i) * Polynomial.X ^ (i : ℕ)).eval b = 0 ∧
        (Polynomial.X ^ n +
          ∑ i : Fin n, Polynomial.C (d i) * Polynomial.X ^ (i : ℕ)).derivative.eval b ≠ 0 := by
  sorry

end Valued
