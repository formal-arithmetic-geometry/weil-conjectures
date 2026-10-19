/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Polynomial and affinoid completed local rings

Source: Temkin, Stable modification of relative curves, Theorem 3.5.5, Step 3,
printed p. 22 (blueprint: lem-trf-affinoid-polynomial-closed-point-comparison).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- The canonical inclusion of polynomials into restricted series, using the actual
constants and variables. Source: Temkin, Theorem 3.5.5, Step 3, printed p. 22
(blueprint: lem-trf-affinoid-polynomial-closed-point-comparison). -/
noncomputable def polynomialInclusion
    (F : Type u) [NormedField F] [IsUltrametricDist F] (n : ℕ) :
    MvPolynomial (Fin n) F →+*
      ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) :=
  MvPolynomial.eval₂Hom (constants F n)
    (fun i ↦ ⟨MvPowerSeries.X i, MvPowerSeries.isRestricted_monomial _ _ _⟩)

/-- The canonical map from the polynomial quotient to the corresponding restricted-series
quotient. Source: Temkin, Theorem 3.5.5, Step 3, printed p. 22
(blueprint: lem-trf-affinoid-polynomial-closed-point-comparison). -/
noncomputable def polynomialQuotientMap
    (F : Type u) [NormedField F] [IsUltrametricDist F] (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) F)) :
    (MvPolynomial (Fin n) F ⧸ J) →+*
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) ⧸
        J.map (polynomialInclusion F n)) :=
  Ideal.quotientMap _ (polynomialInclusion F n) Ideal.le_comap_map

/-- Closed ideals, the complete quotient Gauss norm, and the canonical comparison of
completed local rings. The normed structures in the conclusion have the original ring
operations and the specified Gauss/quotient norms; they are not assumptions.
Source: Temkin, Theorem 3.5.5, Step 3, printed p. 22
(blueprint: lem-trf-affinoid-polynomial-closed-point-comparison).

Proof (the node's agent reconstruction of the analytic input).
1. Coefficient decay is preserved by finite Cauchy products. Coefficientwise limits of
Gauss-Cauchy sequences are restricted, proving completeness and polynomial density.
The geometric series in a series of norm less than one gives an inverse to one minus it.
2. Normalize a nonzero series by a largest coefficient. A triangular change of variables
separates the finitely many largest terms. The leading coefficient is a unit of norm one;
apply lem-trf-tate-weierstrass-norm-division to obtain a monic distinguished polynomial.
3. Induct on the number of variables to prove bounded finite generation for submodules
of every finite free module. For zero variables, a nonsingular basis minor bounds the
coordinates of each vector.
4. For an ideal containing a distinguished polynomial, divide by it. The remainders form
a submodule of a finite free module over the ring with one fewer variable. Its bounded
generators together with the polynomial generate the ideal with a uniform bound.
5. Induct on module rank by projection onto the last coordinate. Lift bounded generators
of its image ideal; the kernel has smaller rank. This completes both inductions.
6. Ideals are finitely generated. A telescoping sequence approaching a point of their
closure, expressed in bounded generators, has convergent coefficient sums. Hence ideals
are closed, and their quotients are Noetherian (def-weil-pbc-noetherian-ring).
7. The infimum over representatives is separated by closedness. It is submultiplicative,
ultrametric and homogeneous. Lift a rapidly Cauchy subsequence's differences with
summable norms to prove quotient completeness. The zero quotient is included.
8. Distinguished division makes each maximal residue field finite over a ring with one
fewer variable. Integrality of finite algebras (lem-weil-pbc-finite-algebra-is-integral)
shows the image of that ring is a field; induction proves finiteness over F.
9. The coordinate images in that field have bounded powers. Apply
lem-trf-finite-extension-bounded-powers-polynomial to obtain monic annihilating
polynomials in each coordinate with all coefficient norms at most one.
10. Divide successively by the kth powers of those polynomials. The commuting remainder
operators identify the polynomial and restricted-series quotients with the same finite
rectangular monomial span, including the constants when there are zero variables.
11. Ideal correspondence first proves maximality of the contraction and then identifies
B/p^k with C/m^k through the actual polynomial inclusion for every positive k.
12. Localization at a maximal ideal does not change these quotients: a geometric finite
sum inverts any denominator outside the ideal. These compatible identifications give
inverse maps on compatible sequences (def-weil-pbc-adic-completion). The displayed
finite-residue characterization identifies the resulting isomorphism with the map
induced by Localization.localRingHom (def-weil-pbc-localization-at-prime).
-/
theorem affinoid_polynomial_closed_point_comparison
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1) (n : ℕ)
    (J : Ideal (MvPolynomial (Fin n) F)) :
    (∃ N : NormedCommRing
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))),
      N.toCommRing = (inferInstance : CommRing
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ)))) ∧
      (∀ s, @norm _ N.toNorm s =
        MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) s.val) ∧
      @IsClosed _ N.toUniformSpace.toTopologicalSpace (J.map (polynomialInclusion F n) : Set _) ∧
      ∃ Q : NormedCommRing
          (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) ⧸
            J.map (polynomialInclusion F n)),
        Q.toCommRing = (inferInstance : CommRing
          (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) ⧸
            J.map (polynomialInclusion F n))) ∧
        @CompleteSpace _ Q.toUniformSpace ∧
        (∀ c, @norm _ Q.toNorm c = sInf {r : ℝ | ∃ s,
          Ideal.Quotient.mk (J.map (polynomialInclusion F n)) s = c ∧
          r = MvPowerSeries.gaussNorm (norm : F → ℝ) (fun _ : Fin n ↦ 1) s.val}) ∧
        ∃ A : @NormedAlgebra F _ inferInstance Q.toSeminormedRing,
          ∀ a : F, A.toAlgebra.algebraMap a =
            Ideal.Quotient.mk (J.map (polynomialInclusion F n)) (constants F n a)) ∧
    IsNoetherianRing
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) ⧸
        J.map (polynomialInclusion F n)) ∧
    ∀ (m : Ideal
        (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin n ↦ (1 : ℝ))) ⧸
          J.map (polynomialInclusion F n))) [m.IsMaximal],
      (m.comap (polynomialQuotientMap F n J)).IsMaximal ∧
      ∃ e : AdicCompletion
          (IsLocalRing.maximalIdeal
            (Localization.AtPrime (m.comap (polynomialQuotientMap F n J))))
          (Localization.AtPrime (m.comap (polynomialQuotientMap F n J))) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Localization.AtPrime m),
        ∀ (k : ℕ)
          (x : AdicCompletion
            (IsLocalRing.maximalIdeal
              (Localization.AtPrime (m.comap (polynomialQuotientMap F n J))))
            (Localization.AtPrime (m.comap (polynomialQuotientMap F n J))))
          (a : Localization.AtPrime (m.comap (polynomialQuotientMap F n J))),
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal
                (Localization.AtPrime (m.comap (polynomialQuotientMap F n J)))) k x =
            Ideal.Quotient.mk
              (IsLocalRing.maximalIdeal
                (Localization.AtPrime (m.comap (polynomialQuotientMap F n J))) ^ k) a →
          AdicCompletion.evalₐ (IsLocalRing.maximalIdeal (Localization.AtPrime m)) k (e x) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime m) ^ k)
              (Localization.localRingHom (m.comap (polynomialQuotientMap F n J)) m
                (polynomialQuotientMap F n J) rfl a) := by
  sorry

end RestrictedSeries
