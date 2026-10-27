/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.FieldTheory.Perfect
public import Sheaf.AlgebraicGeometry.IsRegularScheme
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import WeilConjectures.LinearAlgebra.NonzeroMaximalMinorOfInjective
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Local Jacobian charts over a perfect complete nonarchimedean field

Source: Temkin, Desingularization of quasi-excellent schemes in characteristic zero,
Proposition 3.3.1 proof, printed p. 19, and Proposition 3.3.2 proof, printed pp. 20--21;
Conrad, Irreducible components of rigid spaces, Lemma 3.3.1 proof, printed p. 510
(blueprint: lem-per-perfect-affinoid-local-jacobian-chart).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace RestrictedSeries

/-- Every closed point of a regular affinoid quotient over a perfect field has a
Jacobian minor and a colon-ideal certificate that are both nonzero there. The equality
for `D.val` specifies the determinant using termwise formal derivatives, the actual
inclusion of the restricted-series subring, and increasing enumerations of both subsets.
It uniquely determines `D`; it does not substitute an arbitrary element for the minor.
The quantified condition on `a` is exactly membership in `(I_E : I)`.

Source: Temkin, Proposition 3.3.1 proof, printed p. 19, Proposition 3.3.2 proof,
printed pp. 20--21; Conrad, Lemma 3.3.1 proof, printed p. 510
(blueprint: lem-per-perfect-affinoid-local-jacobian-chart).

Proof (the node's agent reconstruction).
1. If the quotient is zero, there is no maximal ideal. Otherwise pull the given maximal
ideal back to the restricted-series ring. Apply
lem-trf-affinoid-polynomial-closed-point-comparison with polynomial ideal zero.
The polynomial contraction is maximal and its completed local ring is the completed
local ring of the series ring. Polynomial Noetherianity
(lem-weil-pbc-finite-type-algebra-noetherian), localization Noetherianity
(lem-weil-pbc-localization-noetherian), and preservation of residue fields by local
completion (lem-weil-pbc-local-completion-local-ring) identify their residue fields.
Zariski's lemma (lem-weil-pbc-zariski-lemma) makes this residue field finite over F.
2. Perfectness makes this extension separable. Regularity gives a regular local quotient
at the point (def-weil-regular-scheme). Apply
lem-per-separable-regular-affinoid-residual-conormal to inject I/nI into the r-dimensional
residue vector space by the termwise derivatives. These derivatives are restricted:
their coefficients are shifted coefficients multiplied by natural numbers of norm at
most one, so coefficient decay is preserved.
3. The classes of the given relations span I/nI. Choose a basis among them using
lem-weil-span-independent-subfamily. Its index subset E gives independent Jacobian
columns over the residue field.
4. Localize I at the pulled-back maximal ideal using def-weil-pbc-module-localization
and def-weil-pbc-localization-at-prime. Identify its quotient by the maximal ideal with
I/nI by g/u mapping to the inverse of the residue of u times [g]; the inverse sends [g]
to [g/1]. Apply lem-weil-pbc-nakayama-local-generators to the chosen basis to see that
the E-relations generate the localized ideal.
5. For each original relation clear the finitely many denominators of an expression
in the chosen generators. The localization zero criterion supplies another multiplier
outside n killing the remaining error. Multiply these finitely many multipliers to
obtain a outside n with aI contained in I_E. Empty products are one.
6. Apply lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor to the independent
columns, obtaining a row subset U of the same size and a nonzero minor. The Leibniz
formula (def-weil-pbc-matrix-determinant) commutes with reduction. Its determinant D
therefore lies outside n. The restricted subring is closed under the finite sums and
products in this determinant. The empty determinant is one.
7. The residues of a and D in the residue field are nonzero, so their product is nonzero.
This is the required nonmembership in m. The subsets may vary with m, so no
equidimensionality is needed. For I = 0 or r = 0 the empty subsets are allowed. -/
theorem perfect_affinoid_local_jacobian_chart
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [PerfectField F] (hF : ∃ c : F, c ≠ 0 ∧ ‖c‖ ≠ 1) (r s : ℕ)
    (f : Fin s → ↥(MvPowerSeries.IsRestricted.subring (R := F)
      (fun _ : Fin r ↦ (1 : ℝ))))
    [IsRegularRing
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸
        Ideal.span (Set.range f))]
    (m : Ideal
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸
        Ideal.span (Set.range f))) [m.IsMaximal] :
    ∃ (E : Finset (Fin s)) (U : Finset (Fin r)) (h : U.card = E.card)
      (a D : ↥(MvPowerSeries.IsRestricted.subring (R := F)
        (fun _ : Fin r ↦ (1 : ℝ)))),
      (∀ b ∈ Ideal.span (Set.range f), a * b ∈ Ideal.span (f '' (E : Set (Fin s)))) ∧
      D.val = Matrix.det (fun i j : Fin E.card ↦
        MvPowerSeries.pderiv F (U.orderEmbOfFin h i) (f (E.orderEmbOfFin rfl j)).val) ∧
      Ideal.Quotient.mk (Ideal.span (Set.range f)) a *
        Ideal.Quotient.mk (Ideal.span (Set.range f)) D ∉ m := by
  sorry

end RestrictedSeries
