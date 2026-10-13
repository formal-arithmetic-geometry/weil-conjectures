/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Lifting a finite coefficient basis through exponent residues

Source: Stacks Project, Tag 07P5, first proof paragraph, with the explicit basis
construction in lem-weil-pbc-power-series-subring-finite-basis, step 2.
(blueprint: lem-weil-pbc-power-series-residue-monomial-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

/-- A finite coefficient-field basis lifts to the explicit residue-monomial basis.
Source: Stacks Project, Tag 07P5, finiteness paragraph, expanded by the explicit
coefficient-grouping argument in the parent node, step 2.
(blueprint: lem-weil-pbc-power-series-residue-monomial-basis).

Proof: For each polynomial exponent g and series exponent a write a = p*A + e
and g = p*G + h coordinatewise, with all entries of e and h less than p. Expand
each coefficient uniquely in b. For a fixed triple (q,e,h), put the q-coordinate
of the coefficient at (p*A+e,p*G+h) into a new column at (p*A,p*G), and put zero
at the other exponents. Each column lies in S by hS. There are only finitely many
triples, since the coefficient basis and both residue sets are finite. Moreover,
only finitely many polynomial exponents G occur: they are coordinatewise quotients
of the finitely many polynomial exponents of the original polynomial. Thus each
column really is a polynomial with power-series coefficients. Summing the columns
times the indicated monomials recovers every coefficient, proving spanning.
For uniqueness, take a relation among these monomials with coefficients in S.
At exponent (p*A+e,p*G+h), support divisibility means only the terms with residues
(e,h) contribute. Their coefficient is the sum of b(q) times the corresponding
K coordinates of the columns. Independence of b makes every such coordinate
zero. Varying A,G,e,h and using the support condition proves that all columns
are zero. This gives the claimed basis, with exactly the displayed values.
The proof uses only positivity of p, not characteristic p. For p=1 the residue
sets are singletons; zero variables give empty products and the same argument. -/
theorem powerSeriesResidueMonomialBasis
    (p : ℕ) (hp : 0 < p)
    (k : Type u) [Field k] (K : Subfield k)
    (Q : Type v) [Finite Q] (b : Module.Basis Q K k)
    (n m : ℕ)
    (S : Subring (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)))
    (hS : ∀ f, f ∈ S ↔
      ∀ (a : Fin n →₀ ℕ) (g : Fin m →₀ ℕ),
        MvPowerSeries.coeff a (MvPolynomial.coeff g f) ∈ K ∧
        (MvPowerSeries.coeff a (MvPolynomial.coeff g f) ≠ 0 →
          (∀ i, p ∣ a i) ∧ (∀ j, p ∣ g j))) :
    ∃ B : Module.Basis (Q × (Fin n → Fin p) × (Fin m → Fin p)) S
      (MvPolynomial (Fin m) (MvPowerSeries (Fin n) k)),
      ∀ q, B q =
        MvPolynomial.C (MvPowerSeries.C (b q.1) *
          ∏ i : Fin n, MvPowerSeries.X i ^ (q.2.1 i : ℕ)) *
        ∏ j : Fin m, MvPolynomial.X j ^ (q.2.2 j : ℕ) := by sorry

end RingTheory
