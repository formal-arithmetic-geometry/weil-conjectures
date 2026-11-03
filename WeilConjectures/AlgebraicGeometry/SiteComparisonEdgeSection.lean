/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
-- Terminal comparison comes from the normalized finite-coefficient public import.
-- The full proof-only operations and CohomologicalDimension imports bring duplicate Iso modules.

/-!
# Comparison preserves higher-direct-image edge sections

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md, opening paragraph;
Stacks Tags 099W and 072W
(blueprint: lem-pur-site-comparison-edge-section).

The helpers specialize the existing canonical terminal evaluation, derived-composition
isomorphism and truncation spectral-object edge. The comparison maps are the recorded
adjunction-unit global comparison and the recorded counit-mate direct-image comparison.
No resolution, isomorphism, or comparison map is chosen from a mere existence statement.

## Main statement

* `AlgebraicGeometry.ProEtale.siteComparison_edge_section`: both routes from an etale
  global cohomology class to a pro-etale higher-direct-image section agree.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Terminal evaluation on the small etale site, in the literal form used by the recorded
comparison unit. Source: Stacks Tag 099W and the opening paragraph of the relative Kummer
proof (blueprint: lem-pur-site-comparison-edge-section). -/
abbrev siteComparisonEtaleSections (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))

/-- Terminal evaluation on the small pro-etale site. Source: Stacks Tag 099W and the
opening paragraph of the relative Kummer proof
(blueprint: lem-pur-site-comparison-edge-section). -/
abbrev siteComparisonProEtaleSections (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ) ⋙
    (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))

/-- The etale edge: use the inverse Leray identification and then the canonical left edge
of the derived-sections truncation spectral object. Its target is identified by the
existing truncation/degree-zero-derived isomorphism, so this is the cocycle-to-cohomology-
sheaf section map of Stacks Tag 072W. Source: relative Kummer proof, opening paragraph
(blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonEtaleEdge (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (siteComparisonEtaleSections V Λ).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  letI : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsGE 0 :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
      ((DerivedCategory.isGE_iff _ 0).mpr fun _i hi ↦
        Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hi)
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
      ((siteComparisonEtaleLerayIso Λ f).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
    ((siteComparisonEtaleSections V Λ).hypercohomologySpectralObjectFunctor.obj
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).leftEdge q ≫
    ((siteComparisonEtaleSections V Λ).hypercohomologyLeftEdgeTargetIso q).hom.app
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- The pro-etale edge for the comparison pullback of a sheaf placed in degree zero.
It uses the identical Leray and truncation construction as the etale edge. Exactness
of comparison supplies nonnegative cohomology without assuming preservation of injectives.
Source: Stacks Tag 072W; relative Kummer proof, opening paragraph
(blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonProEtaleEdge (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((siteComparisonProEtaleSections U Λ).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
      (siteComparisonProEtaleSections V Λ).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :=
  letI : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).IsGE 0 :=
    Functor.IsTExact.isGE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t _ _ 0
  letI : ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).IsGE 0 :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
      ((DerivedCategory.isGE_iff _ 0).mpr fun _i hi ↦
        Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hi)
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
      ((siteComparisonProEtaleLerayIso Λ f).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
    ((siteComparisonProEtaleSections V Λ).hypercohomologySpectralObjectFunctor.obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))).leftEdge q ≫
    ((siteComparisonProEtaleSections V Λ).hypercohomologyLeftEdgeTargetIso q).hom.app
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

/-- The degree-q map of the recorded derived-unit global comparison, with the derived
identity functor removed by its canonical isomorphism. Source: Stacks Tag 099W; relative
Kummer proof, opening paragraph (blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonCohomologyMap (U : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((siteComparisonProEtaleSections U Λ).rightDerivedFunctorPlus.obj
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
    ((Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
        ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      (finiteComparisonGlobalSections U Λ).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

/-- Pull back the higher-image section using the actual comparison unit, identify
cohomology through exact comparison, and apply cohomology of the specified counit mate.
The unit on terminal sections is the constant-unit-normalized pullback of a section.
Source: Stacks Tags 099W, 0B65; relative Kummer proof, opening paragraph
(blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonHigherImageSectionMap (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (siteComparisonEtaleSections V Λ).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
      (siteComparisonProEtaleSections V Λ).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :=
  (finiteComparisonGlobalSectionsUnit V Λ).app
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
    (siteComparisonProEtaleSections V Λ).map
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryPlusHomologyFunctorIso
          q).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
    (siteComparisonProEtaleSections V Λ).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map
        ((fixedComparisonDirectImageMatePlus Λ f).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

end AlgebraicGeometry.ProEtale
