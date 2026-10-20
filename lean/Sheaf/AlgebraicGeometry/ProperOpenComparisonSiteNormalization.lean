/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.ProEtaleProperOpenComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-!
# Site normalization of the proper/open comparison

Source: Weil blueprint, sec-smooth-purity/sk-def-sf-operations, order 1484,
first and last proof paragraphs; Stacks Project, Tags 09AF and 099R
(blueprint: lem-sf-proper-open-comparison-site-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Positive-level coefficients are finite by the recorded coefficient theorem.
Source: blueprint order 1484, coefficient convention
(blueprint: lem-sf-proper-open-comparison-site-normalization). -/
noncomputable instance properOpenNormalizationCoefficientFinite (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- The named pro-etale proper/open arrow is the exact site pullback of the specified
etale arrow, with the canonical open-extension comparisons and counit-mate
direct-image comparison in their specified directions.
Source: blueprint order 1484, first and last proof paragraphs; Stacks Tags 09AF, 099R
(blueprint: lem-sf-proper-open-comparison-site-normalization).

Proof: the coefficient instance supplies finiteness at the positive level. Expand
`properOpenProEtaleIsoPlus` into its four specified factors. The comparison functor
and the direct-image mate agree definitionally with `siteComparisonDerivedPullbackPlus`
and `fixedComparisonDirectImageMatePlus`. The hom of each composed isomorphism is
the composite of its homs, and mapping an isomorphism maps its hom. The first factor
is the inverse of the open-extension comparison for j₂. Precomposing with its forward
map cancels this inverse by `Iso.hom_inv_id_app_assoc`, leaving the required three
factors. The existing construction already supplies the exact derived open comparisons
and the invertibility proofs; neither is constructed again here. -/
theorem properOpenComparison_site_normalization (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    {T₁ T₂ X : Scheme.{u}} [IsNoetherian X] [IsNoetherian T₁] [IsNoetherian T₂]
    (f : T₁ ⟶ T₂) [IsProper f]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : j₁ ≫ f = j₂)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :
    (properOpenSiteExtensionIso (Padic.coefficientExtensionRing l E (n + 1)) j₂).hom.app L ≫
        (properOpenProEtaleIsoPlus (Padic.coefficientExtensionRing l E (n + 1))
          f j₁ j₂ h L).hom =
      (siteComparisonDerivedPullbackPlus T₂ (Padic.coefficientExtensionRing l E (n + 1))).map
        (Etale.properOpenComparison (Padic.coefficientExtensionRing l E (n + 1)) f j₁ j₂ h L) ≫
      (fixedComparisonDirectImageMatePlus (Padic.coefficientExtensionRing l E (n + 1)) f).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
            j₁).mapDerivedCategoryPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
        f).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso
            (Padic.coefficientExtensionRing l E (n + 1)) j₁).hom.app L) := by
  simp only [properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, asIso_hom,
    fixedComparisonDirectImageMatePlus, siteComparisonDerivedPullbackPlus,
    Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.ProEtale
