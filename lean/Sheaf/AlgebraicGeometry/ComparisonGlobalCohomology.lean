/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel

/-!
# Global cohomology under the etale to pro-etale comparison

Source: blueprint, `sec-proper-base-change/sk-thm-properbasechange/`
`lem-weil-pbc-comparison-global-cohomology.md`, statement and both proof paragraphs
(blueprint: lem-weil-pbc-comparison-global-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical map on ordinary derived global sections, induced by the bounded-below
comparison unit followed by the Leray isomorphism coming from evaluation at the terminal
objects. The compatibility of bounded-below and unbounded right derived functors transports
that unit into the unbounded derived category. This uses left modules over any finite ring;
no monoidal structure on the coefficient category is required.
Source: blueprint, comparison-global-cohomology, final proof sentence
(blueprint: lem-weil-pbc-comparison-global-cohomology). -/
noncomputable def comparisonGlobalSections (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    DerivedCategory.Plus.ι ⋙ Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus ⋙
        DerivedCategory.Plus.ι ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T :=
  let L := (comparisonUpperStar (ModuleCat.{u + 1} Λ) T).mapDerivedCategoryPlus
  let R := comparisonLowerStar (ModuleCat.{u + 1} Λ) T
  let Γ := Etale.rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) T
  (Functor.leftUnitor (DerivedCategory.Plus.ι ⋙ Γ)).inv ≫
    Functor.whiskerRight (T.proEtaleSiteComparisonModules Λ).derivedPlus.unit
      (DerivedCategory.Plus.ι ⋙ Γ) ≫
    (Functor.associator L R.rightDerivedFunctorPlus (DerivedCategory.Plus.ι ⋙ Γ)).hom ≫
    Functor.whiskerLeft L
      ((Functor.associator R.rightDerivedFunctorPlus DerivedCategory.Plus.ι Γ).inv ≫
        Functor.whiskerRight R.rightDerivedFunctorPlusCompatibility.hom Γ ≫
        (Functor.associator DerivedCategory.Plus.ι R.rightDerivedFunctor Γ).hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          (comparisonLowerStarCompRightDerivedGlobalSectionsIso
            (ModuleCat.{u + 1} Λ) T).hom)

/-- The derived comparison unit induces a natural isomorphism of ordinary global sections.
Source: blueprint, comparison-global-cohomology, statement and proof
(blueprint: lem-weil-pbc-comparison-global-cohomology).

Proof: (1) Exactness of the comparison inverse image, supplied by
`prop-weil-pbc-site-comparison-finite-level`, implies that its right adjoint preserves
injectives. On a bounded-below pro-etale injective resolution, pushforward thus computes
its right derived functor and subsequent derived sections. Evaluation at the final object
identifies the two section complexes termwise. This is the canonical Leray comparison of
`lem-weil-pbc-derived-sections-pushforward`, represented here by
`comparisonLowerStarCompRightDerivedGlobalSectionsIso`.
(2) Apply this comparison to the inverse image of the given bounded-below etale complex.
The derived unit is invertible by `thm-weil-pbc-site-comparison`; applying ordinary etale
derived sections and composing with the Leray isomorphism proves the assertion. All
comparison maps are natural, so their composite is a natural isomorphism. -/
theorem isIso_comparisonGlobalSections (T : Scheme.{u})
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ] :
    IsIso (comparisonGlobalSections T Λ) := by
  sorry

end AlgebraicGeometry.ProEtale
