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
import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Triple
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

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

Proof:
1. The positive-level coefficient ring is finite by def-weil-l-adic-coefficient-extension.
Locally Noetherian schemes are quasi-separated by
lem-weil-pbc-locally-noetherian-quasi-separated. With quasi-compactness, the permanence
lemma lem-weil-pbc-qcqs-morphism-permanence gives the direct-image comparison hypotheses;
alternatively properness directly supplies them. No invertibility of l is required.
2. The canonical adjoint open comparisons of lem-cbc-proetale-extension-zero-comparison
are natural in sheaves. Exactness of both extensions (lem-weil-pbc-extension-by-zero-exact
and lem-weil-extension-by-zero-exact), and exact comparison
(def-sf-comparison-derived-pullback), let these isomorphisms act termwise on complexes.
Naturality respects differentials. Exactness preserves quasi-isomorphisms and lower
cohomology bounds, so they descend to the displayed bounded below comparisons.
3. Apply exact comparison to the specified etale map of
def-weil-pbc-proper-open-comparison. It is invertible by
lem-weil-pbc-proper-open-comparison-iso. At its target use precisely the named comparison
of lem-weil-pbc-comparison-direct-image-canonical-mate, then the direct image of the first
open comparison. Each arrow has the displayed source and target.
4. Expand properOpenProEtaleIsoPlus: it first uses the inverse open comparison for
j₂, then the pulled-back etale arrow, then the canonical direct-image mate, and finally
the direct image of the open comparison for j₁. This is the named construction of
lem-weil-pbc-proper-open-comparison-proetale, not an arbitrary endpoint isomorphism.
5. Precompose with the forward open comparison for j₂. Associativity and cancellation
of that comparison with its inverse yield the equality, in the bounded below derived
category of pro-etale constant-coefficient modules on T₂. -/
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
  sorry

end AlgebraicGeometry.ProEtale
