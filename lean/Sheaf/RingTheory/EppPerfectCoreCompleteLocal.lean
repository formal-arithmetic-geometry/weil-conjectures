/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Algebraic.Defs
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.LaurentSeries

/-!
# The Epp field hypothesis for a complete local domain

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé IV, 3.2.1,
Proposition 3.2.3(i),(iv), and their application in 4.2.3
(blueprint: lem-per-epp-perfect-core-complete-local).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsLocalRing

/-- If the maximal perfect subfield of the residue field of a complete Noetherian
local domain is algebraic over its specified perfect subfield, the maximal perfect
subfield of its fraction field is algebraic over that same subfield. Membership
in either perfect core is written explicitly as existence of all p-power roots.
The algebra structures on the residue and fraction fields are induced by the
specified algebra structure on R; its structure map is injective since k₀ is a field.

Source: ILO, Travaux de Gabber, Exposé IV, 3.2.1 and Proposition 3.2.3(i),(iv),
as applied in 4.2.3.
(blueprint: lem-per-epp-perfect-core-complete-local).

Proof (the seven steps of the DAG, to be formalized in stage 3):
1. Apply lem-weil-pbc-complete-local-domain-finite-over-regular. In characteristic p
   its Cohen parameter subring A is C[[t₁,...,t_d]] for a coefficient field C:
   the prime generator of a mixed-characteristic Cohen ring would be zero or a unit.
   The constant-coefficient residue map identifies C with k = R/m and supplies
   a section s : k → R. A series with nonzero constant coefficient has inverse
   given by its geometric series, so the residue field really is C.
2. For a in k₀, choose a_n in k₀ with a_n^(p^n) = a. The difference
   s(residue a_n) - a_n lies in m, hence s(residue a) - a lies in m^(p^n).
   Separatedness from def-weil-pbc-adically-complete-ring, and cofinality of p^n,
   imply this difference is zero. Thus s preserves the specified k₀. The residue
   isomorphism identifies the perfect cores of C and k, so C's core is algebraic
   over this same k₀ by the hypothesis.
3. Localize the finite A-module R at A minus zero. This is a finite-dimensional
   domain over K = Frac(A). Multiplication by any nonzero element is injective,
   hence surjective, so the localization is a field and equals F = Frac(R).
   Therefore F/K is finite, without any separability assumption.
4. In H((t)), the p^n-th power of a series has coefficients raised to p^n
   and exponents multiplied by p^n. This follows by shifting to a power series,
   truncating at each degree and applying the characteristic-p binomial identity.
   All exponents in the support of an element with roots of every such order
   are divisible by every p^n, hence zero. Its constant lies in the perfect core
   of H. Conversely roots in H give constant roots in H((t)). This includes zero.
5. Group multivariate coefficients successively by the last variable to embed
   A into the iterated Laurent field C((t₁))...((t_d)). Cauchy multiplication
   agrees coefficientwise since each multidegree has finitely many decompositions.
   The embedding extends to K by fractions. Step 4 identifies K's perfect core
   with C's perfect core. For d = 0 this is the identity on C.
6. Apply lem-per-finite-extension-perfect-core to F/K from step 3. Every element
   of F's perfect core is algebraic over K's perfect core, including inseparable
   finite extensions. By step 5 this is C's perfect core.
7. Choose a monic annihilating polynomial for x over C's perfect core. Each of
   its finitely many coefficients is algebraic over k₀ by step 2. Monic equations
   for the coefficients and for x give a finite k₀-spanning set of their generated
   algebra by reducing powers. Linear dependence of sufficiently many powers
   of x yields a nonzero polynomial over k₀ annihilating x. For x = 0 use T. -/
theorem epp_perfect_core_complete_local
    (p : ℕ) [Fact p.Prime] (k₀ : Type v) [Field k₀] [CharP k₀ p]
    [PerfectRing k₀ p] (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] [CharP R p] [Algebra k₀ R]
    [IsAdicComplete (maximalIdeal R) R]
    (hres : ∀ x : ResidueField R,
      (∀ n : ℕ, ∃ y : ResidueField R, y ^ (p ^ n) = x) → IsAlgebraic k₀ x) :
    ∀ x : FractionRing R,
      (∀ n : ℕ, ∃ y : FractionRing R, y ^ (p ^ n) = x) → IsAlgebraic k₀ x := by
  sorry

end IsLocalRing
