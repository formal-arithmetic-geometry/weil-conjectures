/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.MvPowerSeries.Derivative
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.PolynomialRingMaximalLocalizationDimension
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension

/-!
# Cotangent coordinates at a separable closed point of a Tate algebra

Source: Conrad, Several approaches to non-archimedean geometry, Theorem 1.1.5(1),
PDF p.4; separable-point refinement using Irreducible components of rigid spaces,
section 1.1, printed p.477, and proof of Lemma 3.3.1, printed p.510
(blueprint: lem-per-tate-separable-local-cotangent-coordinates).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- The derivative rule identifies the cotangent space at a finite separable closed
point with the coordinate space. The additive equivalence and its scalar equation
express linearity for the quotient scalar structure transported by the residue map.
The derivatives are specified by every coefficient, so no derivative is arbitrary.
Source: Conrad, Theorem 1.1.5(1), PDF p.4, with the separable-point refinement
using Irreducible components of rigid spaces, section 1.1 and Lemma 3.3.1
(blueprint: lem-per-tate-separable-local-cotangent-coordinates).

Proof:
1. By def-weil-pbc-localization-at-prime the localization is local with maximal
ideal nR. Every element of that ideal is h/u with h in n. Reducing numerator and
unit denominator gives a surjective residue map with kernel nR.
2. Apply lem-trf-affinoid-polynomial-closed-point-comparison to the zero ideal.
The polynomial local ring and the Tate local ring have isomorphic completions.
Use lem-weil-pbc-localization-noetherian for Noetherianity, the regularity of the
polynomial ring (lem-weil-pbc-polynomial-ring-field-regular-ring), and
lem-weil-pbc-polynomial-ring-maximal-localization-dimension for dimension r.
Then lem-weil-pbc-completion-regular-local and lem-weil-pbc-completion-dimension
imply that the Tate local ring is regular and has dimension r.
3. The coefficient formula for termwise differentiation preserves restrictedness:
the ultrametric inequality bounds every natural-number scalar by one. Finite
Cauchy sums prove the Leibniz rule. Extend each residue-valued derivative to
fractions by the quotient rule. Differentiating a clearing relation proves that
it is independent of the representative.
4. Leibniz shows that these derivatives kill the square of the maximal ideal
and that multiplication by a in R acts through rho(a). They therefore give the
stated linear map and the displayed numerator-only formula for h in n.
5. For each coordinate residue a_i, its minimal polynomial f_i is separable,
so f_i'(a_i) is nonzero. The element f_i(x_i) in n maps to f_i'(a_i) times the
ith standard vector. Scaling by its inverse proves surjectivity.
6. By lem-weil-pbc-regular-local-cotangent-dimension the source has dimension r.
The target also has dimension r, so the surjection is an isomorphism. For r=0,
constant coefficients identify T with F, the maximal ideal is zero, localization
and residue field identify with F, and both vector spaces are zero.
-/
theorem tate_separable_local_cotangent_coordinates
    (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
    (hF : ∃ a : F, a ≠ 0 ∧ ‖a‖ ≠ 1) (r : ℕ)
    (n : Ideal ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
    [n.IsMaximal]
    (hfinite : @Module.Finite F
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) _ _
      ((Ideal.Quotient.mk n).comp (constants F r)).toAlgebra.toModule)
    (hseparable : @Algebra.IsSeparable F
      (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n) _ _
      ((Ideal.Quotient.mk n).comp (constants F r)).toAlgebra) :
    IsRegularLocalRing (Localization.AtPrime n) ∧
    n.map (algebraMap ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))
        (Localization.AtPrime n)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime n) ∧
    (∃ d : Fin r → ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) →
        ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))),
      (∀ (i : Fin r)
          (h : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))),
        (d i h).val = MvPowerSeries.pderiv F i h.val) ∧
      ∃ ρ : Localization.AtPrime n →+*
          (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n),
        Function.Surjective ρ ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime n) ∧
        (∀ (h : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))))
            (v : n.primeCompl),
          ρ (IsLocalization.mk' (Localization.AtPrime n) h v) =
            @Div.div _ (Ideal.Quotient.field n).toDiv
              (Ideal.Quotient.mk n h) (Ideal.Quotient.mk n v.val)) ∧
        ∃ θ : IsLocalRing.CotangentSpace (Localization.AtPrime n) ≃+
            (Fin r → ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n),
          (∀ (a : Localization.AtPrime n)
              (z : IsLocalRing.CotangentSpace (Localization.AtPrime n)) (i : Fin r),
            θ (a • z) i = ρ a * θ z i) ∧
          ∀ (h : n) (v : n.primeCompl)
              (z : IsLocalRing.maximalIdeal (Localization.AtPrime n)),
            z.val = IsLocalization.mk' (Localization.AtPrime n) h.val v →
            ∀ i : Fin r,
              θ ((IsLocalRing.maximalIdeal (Localization.AtPrime n)).toCotangent z) i =
                @Div.div _ (Ideal.Quotient.field n).toDiv
                  (Ideal.Quotient.mk n (d i h.val)) (Ideal.Quotient.mk n v.val)) ∧
    (r = 0 → n = ⊥ ∧ IsLocalRing.maximalIdeal (Localization.AtPrime n) = ⊥ ∧
      ∃ (eT : ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ≃+* F)
          (eR : Localization.AtPrime n ≃+* F)
          (eκ : (↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n)
            ≃+* F),
        (∀ a : F, eT (constants F r a) = a) ∧
        (∀ a : F, eR (algebraMap
          ↥(MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin r ↦ (1 : ℝ)))
          (Localization.AtPrime n) (constants F r a)) = a) ∧
        (∀ a : F, eκ (Ideal.Quotient.mk n (constants F r a)) = a) ∧
        Subsingleton (IsLocalRing.CotangentSpace (Localization.AtPrime n)) ∧
        Subsingleton
          (Fin r → ↥(MvPowerSeries.IsRestricted.subring (R := F)
            (fun _ : Fin r ↦ (1 : ℝ))) ⧸ n)) := by
  sorry

end RestrictedSeries
