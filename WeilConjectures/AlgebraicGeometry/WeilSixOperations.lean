/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFunctorPackage
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedSfBidualityClass
public import WeilConjectures.AlgebraicGeometry.CondensedSixFunctorOperationDatum

/-! # The assembled operations for the global finite-field datum

Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
thm-weil-six-operations.md (blueprint: thm-weil-six-operations).

The geometric base is the fixed algebraic closure in `FiniteFieldDatum`. All four
coefficient stages and every domain remain those of the coefficient-and-functor package.
The characteristic of the fixed algebraic closure is the prime `D.p`.
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace WeilConjectures

/-- Export all seven clauses on their original domains to the global finite-field datum.
Finite coefficients use the actual constructible finite-Tor category, and higher
coefficients use the ordinary condensed bounded constructible category. General Hom
comparison and exceptional adjunction use their stated constructible domains; the
sharper Hom interval keeps the site-perfect first-variable hypothesis. The package's
biduality field specifies the internal Hom into the exceptional image of the coefficient
unit, an exact anti-equivalence, and invertibility of the evaluation-defined natural map.

Source: latest blueprint, thm-weil-six-operations and its terminal-assembly proof
(blueprint: thm-weil-six-operations).

Proof plan:
1. Identify the geometric base and coefficient prime of def-fix-six-functor-datum with
   the fixed algebraic closure `D.k` and `ell`. Algebra.ringChar_eq identifies the
   characteristic with that of the finite field `D.k₀`.
2. Apply prop-functor-package with exactly these parameters. Retain its seven clauses,
   all coefficient comparisons and all bounds, in particular the site-perfect Hom
   hypothesis, the proper-or-smooth alternative for ordinary exchange, the torsion
   bounded-below finite domain, and finite Tor on the second projection factor.
3. Its ordinary condensed biduality clause is the coefficient-class assertion of
   thm-sf-biduality-class: the dualizing object is the exceptional image of the unit
   and its biduality map is the transpose of evaluation. At finite coefficients its
   domain is Dctf; integrally and at the field stages it is the specified Dbc.
-/
theorem weilSixOperations (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hchar : ell ≠ D.p) :
    @AlgebraicGeometry.ProEtale.CondensedRing.CondensedFunctorPackage.{u} ell _ D
      ⟨hchar⟩ ∧
    type_of% (@AlgebraicGeometry.ProEtale.CondensedRing.condensedSfBidualityClass.{u}
      D ell _ ⟨hchar⟩) := by
  sorry

end WeilConjectures
