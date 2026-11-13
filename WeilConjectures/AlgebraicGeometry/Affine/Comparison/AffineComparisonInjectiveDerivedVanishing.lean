/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonEtaleCechPresentation
import WeilConjectures.AlgebraicGeometry.AffineEtaleCechSystem.AffineComparisonCategoricalCechSystem
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalInjectiveCechExactness
import WeilConjectures.CategoryTheory.Sites.Categorical.CategoricalFiniteCechCriterion
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonInjectiveVanishing

/-!
# Affine comparison vanishing for Grothendieck abelian coefficients

The categorical form of the finite Čech argument in Stacks Project, Tag 099U.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- On an affine scheme, the comparison pullback of an injective étale sheaf has zero
positive derived global sections, with Grothendieck abelian coefficients.
Source: Stacks Project, Tag 099U, finite Čech proof with exact filtered colimits. -/
theorem isZero_rightDerived_globalSections_comparisonUpperStar_of_isAffine
    (X : Scheme.{u}) [IsAffine X]
    (I : Sheaf X.smallEtaleTopology A) [Injective I] (q : ℕ) :
    IsZero (((sheafToPresheaf (Scheme.ProEt.topology X) A ⋙
      (evaluation X.ProEtᵒᵖ A).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X)
        (MorphismProperty.id_mem _ X)))).rightDerived (q + 1)).obj
      ((comparisonUpperStar A X).obj I)) := by
  have : Injective I.obj := (sheafificationAdjunction X.smallEtaleTopology A).map_injective
    I inferInstance
  apply CategoryTheory.Sheaf.isZero_rightDerived_eval_of_finiteCech
    (fun V : X.ProEt ↦ proAffineEtale V.hom) _ ((comparisonUpperStar A X).obj I) _
    _ (Scheme.AffineProEt.ofEtale (𝟙 X)).prop q
  · intro V hV R hR
    obtain ⟨n, U, hU, hUR, hcover⟩ := affineProEt_finite_refinement X V hV R hR
    exact ⟨n, U, fun k y ↦ affineProEt_cechNerve X V hV U hU k y, hUR, hcover⟩
  · intro V hV n U hnerve hcover k
    obtain ⟨D, hD, hfilter, S, hS⟩ :=
      exists_affine_etale_cech_system X V hV U hnerve hcover
    exact S.categoricalOriginalExactAt I hS k (fun i ↦
      Presheaf.exactAt_categoricalCech_of_injective I.obj
        (fun b ↦ Over.mk (S.f i b)) k)

end AlgebraicGeometry.ProEtale
