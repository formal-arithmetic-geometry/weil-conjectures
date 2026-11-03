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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
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

universe u uB vB uC vC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{vC} C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- Naturality of the normalized edge, including its canonical target isomorphism.
Source: functoriality of truncation spectral objects
(blueprint: lem-pur-site-comparison-edge-section).

Proof: compose spectral left-edge naturality with naturality of the canonical
truncation/shift/degree-zero target isomorphism. -/
private theorem edge_naturality {K L : DerivedCategory.Plus B}
    [K.IsGE 0] [L.IsGE 0] (b : K ⟶ L) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C q).map (G.rightDerivedFunctorPlus.map b) ≫
      (G.hypercohomologySpectralObjectFunctor.obj L).leftEdge q ≫
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app L =
    (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge q ≫
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
      G.map ((DerivedCategory.Plus.homologyFunctor B q).map b) := by
  have hn := Abelian.SpectralObject.leftEdge_naturality
    (G.hypercohomologySpectralObjectFunctor.map b) (q : ℤ)
  have ht := (G.hypercohomologyLeftEdgeTargetIso q).hom.naturality b
  dsimp only [Functor.comp_map, Abelian.SpectralObject.hFunctor] at ht
  change (DerivedCategory.Plus.homologyFunctor C q).map (G.rightDerivedFunctorPlus.map b) ≫
      (G.hypercohomologySpectralObjectFunctor.obj L).leftEdge q = _ at hn
  rw [reassoc_of% hn, ht]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1600000 in
-- Kernel conversion checks the canonical site and derived-composition data.
/-- Etale/pro-etale comparison preserves the higher-direct-image edge section of each
cohomology class. The two edges are the canonical Leray/truncation edges, the global
comparison is induced by the derived unit, and the section comparison uses the specified
counit mate and exact-cohomology identification.
Source: relative Kummer proof, opening paragraph; Stacks Tags 099W, 072W and 0B65
(blueprint: lem-pur-site-comparison-edge-section).

Proof:
1. Put K = F[0], C = Rf_et,* K and D = Rf_proet,* A_U K. Left exactness
and exact comparison make C, A_V C and D nonnegative. The canonical mate gives
b : A_V C → D.
2. The named Leray/mate compatibility identifies the normalized global comparison
at U followed by inverse pro-etale Leray with inverse etale Leray, normalized
global comparison at V, and derived pro-etale sections of b.
3. Apply naturality of the pro-etale truncation spectral edge and its canonical
target isomorphism to b. The exact-comparison edge lemma moves normalized global
comparison at V through the remaining edge; on the target it is the comparison
unit followed by the exact-cohomology identification.
4. Associate these equalities and evaluate the resulting equality of module
homomorphisms at x. The target composite is the stipulated higher-image section
comparison, including H^q(b). All operations also apply when q=0. -/
theorem siteComparison_edge_section (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    siteComparisonProEtaleEdge Λ f F q (siteComparisonCohomologyMap U Λ F q x) =
      siteComparisonHigherImageSectionMap Λ f F q (siteComparisonEtaleEdge Λ f F q x) := by
  classical
  let G := siteComparisonEtaleSections V Λ
  let G' := siteComparisonProEtaleSections V Λ
  let β := comparisonUpperStar (ModuleCat.{u + 1} Λ) V
  let K := (DerivedCategory.Plus.singleFunctor
    (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  let C := (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K
  let C' := β.mapDerivedCategoryPlus.obj C
  let D := (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q
  let b : C' ⟶ D := (fixedComparisonDirectImageMatePlus Λ f).app K
  have hC : C.IsGE 0 :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
      ((DerivedCategory.isGE_iff _ 0).mpr fun _i hi ↦
        Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hi)
  have hC' : C'.IsGE 0 := Functor.IsTExact.isGE_obj
    DerivedCategory.Plus.TStructure.t DerivedCategory.Plus.TStructure.t _ _ 0
  have hK : ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K).IsGE 0 :=
    Functor.IsTExact.isGE_obj DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t _ _ 0
  have hD : D.IsGE 0 :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
      ((DerivedCategory.isGE_iff _ 0).mpr fun _i hi ↦
        Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE _ _ 0 hi)
  let c := (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
      ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj K) ≫
    (finiteComparisonGlobalSections U Λ).app K
  let τ := (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
      (G.rightDerivedFunctorPlus.obj C) ≫ (finiteComparisonGlobalSections V Λ).app C
  let le := (siteComparisonEtaleLerayIso Λ f).inv.app K
  let lp := (siteComparisonProEtaleLerayIso Λ f).inv.app
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K)
  let ec := (G.hypercohomologySpectralObjectFunctor.obj C).leftEdge q ≫
    (G.hypercohomologyLeftEdgeTargetIso q).hom.app C
  let ec' := (G'.hypercohomologySpectralObjectFunctor.obj C').leftEdge q ≫
    (G'.hypercohomologyLeftEdgeTargetIso q).hom.app C'
  let ed := (G'.hypercohomologySpectralObjectFunctor.obj D).leftEdge q ≫
    (G'.hypercohomologyLeftEdgeTargetIso q).hom.app D
  let unitMap := (finiteComparisonGlobalSectionsUnit V Λ).app
    ((DerivedCategory.Plus.homologyFunctor _ q).obj C)
  let cohomologyMap := G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app C)
  let m := unitMap ≫ cohomologyMap
  let d := G'.map ((DerivedCategory.Plus.homologyFunctor _ q).map b)
  have hn := Abelian.SpectralObject.leftEdge_naturality
    (G'.hypercohomologySpectralObjectFunctor.map b) (q : ℤ)
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).map
      (G'.rightDerivedFunctorPlus.map b) ≫
      (G'.hypercohomologySpectralObjectFunctor.obj D).leftEdge q = _ at hn
  have ht := (G'.hypercohomologyLeftEdgeTargetIso q).hom.naturality b
  dsimp only [Functor.comp_map, Abelian.SpectralObject.hFunctor] at ht
  have he := Functor.hypercohomologyLeftEdge_exactComparison G G' β
    (finiteComparisonGlobalSectionsUnit V Λ) C q
  have hl : c ≫ lp = le ≫ τ ≫ G'.rightDerivedFunctorPlus.map b := by
    simpa only [c, lp, le, τ, Category.assoc] using EdgeComparison.leray_mate Λ f K
  have he : H.map τ ≫ ec' = ec ≫ unitMap ≫ cohomologyMap := by
    simpa only [H, τ, ec, ec', unitMap, cohomologyMap,
      finiteComparisonGlobalSections, Functor.normalizedDerivedBaseChange,
      NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Category.id_comp, Functor.map_comp,
      Category.assoc] using
      Functor.hypercohomologyLeftEdge_exactComparison G G' β
        (finiteComparisonGlobalSectionsUnit V Λ) C q
  have hmain : H.map c ≫ H.map lp ≫ ed = H.map le ≫ ec ≫ unitMap ≫
      cohomologyMap ≫ d := by
    calc
      _ = H.map (c ≫ lp) ≫ ed := by simp only [Functor.map_comp, Category.assoc]
      _ = H.map (le ≫ τ ≫ G'.rightDerivedFunctorPlus.map b) ≫ ed := by rw [hl]
      _ = H.map le ≫ H.map τ ≫
          (H.map (G'.rightDerivedFunctorPlus.map b) ≫ ed) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = H.map le ≫ H.map τ ≫ (ec' ≫ d) := by
        rw [reassoc_of% hn]
        rw [ht]
        rfl
      _ = H.map le ≫ (H.map τ ≫ ec') ≫ d := by simp only [Category.assoc]
      _ = _ := by rw [he]; simp only [Category.assoc]
  have hmap : siteComparisonCohomologyMap U Λ F q ≫
      siteComparisonProEtaleEdge Λ f F q =
      siteComparisonEtaleEdge Λ f F q ≫ siteComparisonHigherImageSectionMap Λ f F q := by
    change H.map c ≫ H.map lp ≫ ed =
      (H.map le ≫ ec) ≫ unitMap ≫ cohomologyMap ≫ d
    simpa only [Category.assoc] using hmain
  exact congrArg (fun g ↦ g x) hmap

end AlgebraicGeometry.ProEtale
