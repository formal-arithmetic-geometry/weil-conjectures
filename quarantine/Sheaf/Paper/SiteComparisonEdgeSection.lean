/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
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

/-- The canonical Leray identification, obtained by deriving the terminal-sections
identification with its unit normalization. Source: Stacks Tag 072W and the opening
paragraph of the relative Kummer proof
(blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonEtaleLerayIso (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V) :
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (siteComparisonEtaleSections V Λ).rightDerivedFunctorPlus ≅
    (siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso' _ _
    (Functor.isoWhiskerLeft _
      ((Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ)
        (Scheme.Etale.isTerminalMkId V)) ≪≫ sheafSectionsNatIsoEvaluation _ _).symm ≪≫
      Etale.lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f ≪≫
      Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ) (Scheme.Etale.isTerminalMkId U) ≪≫
      sheafSectionsNatIsoEvaluation _ _)

/-- The pro-etale Leray identification with the same derived-unit normalization.
Source: Stacks Tags 099W, 072W and the opening paragraph of the relative Kummer proof
(blueprint: lem-pur-site-comparison-edge-section). -/
def siteComparisonProEtaleLerayIso (Λ : Type (u + 1)) [CommRing Λ] {U V : Scheme.{u}} (f : U ⟶ V) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus ⋙
      (siteComparisonProEtaleSections V Λ).rightDerivedFunctorPlus ≅
    (siteComparisonProEtaleSections U Λ).rightDerivedFunctorPlus :=
  letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
  Functor.rightDerivedFunctorPlusCompIso' _ _
    (Functor.isoWhiskerLeft _
      ((Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ)
        (Scheme.ProEt.isTerminalMkId V)) ≪≫ sheafSectionsNatIsoEvaluation _ _).symm ≪≫
      ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} Λ) f ≪≫
      Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ) (Scheme.ProEt.isTerminalMkId U) ≪≫
      sheafSectionsNatIsoEvaluation _ _)

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

/-- Etale/pro-etale comparison preserves the higher-direct-image edge section of each
cohomology class. The two edges are the canonical Leray/truncation edges, the global
comparison is induced by the derived unit, and the section comparison uses the specified
counit mate and exact-cohomology identification.
Source: relative Kummer proof, opening paragraph; Stacks Tags 099W, 072W and 0B65
(blueprint: lem-pur-site-comparison-edge-section).

Proof:
1. Put K = F[0]. By prop-pur-kinjective-resolutions-exist choose K -> I and
A_U I -> J K-injective resolutions. Exactness (lem-sf-comparison-pullback-exact)
makes J represent A_U K. The adjoint h : I -> nu_U,* J represents the derived unit;
evaluation at the terminal object represents the recorded global comparison
(lem-weil-pbc-comparison-global-cohomology and
lem-weil-pbc-derived-sections-pushforward). No preservation of injectives by A_U is used.
2. Put C = u_et,* I and D = u_proet,* J. Both composites of restriction direct images
evaluate on W/V as J(W times_V U), with the same restriction maps
(def-weil-pbc-direct-image, def-weil-pbc-proetale-operations). Transpose u_et,* h using
that canonical identity to obtain d : A_V C -> D (def-weil-pbc-adjunction-mate).
The adjunction formula gives d(A_V z) = h(z) on terminal sections.
3. Identify Q(d) with the named b. The canonical pullback comparison is the conjugate
of this restriction identity (lem-weil-pbc-comparison-pullback,
def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation).
Writing a : A_U u_et^* -> u_proet^* A_V, transpose successively under the two
adjunctions. For v = epsilon_proet,J followed after u_proet^* d, the Hom-bijection
chain gives v a_C = t A_U(epsilon_et,I): the successive adjoints are d, u_et,* h,
h epsilon_et,I, then t A_U(epsilon_et,I), by naturality and the triangle identity.
Localizing and identifying QJ with A_U F using Qt gives exactly the specified counit
normalization of lem-weil-pbc-comparison-direct-image-canonical-mate. Injectivity of
the adjunction bijection identifies Q(d) with that named component.
4. Represent x by a global degree-q cocycle z. The etale edge section is [z] in H^q C
and the pro-etale edge of the global comparison is [h(z)] in H^q D (Stacks Tag 072W).
Exactness of A_V identifies A_V H^q C with H^q(A_V C). Cohomology sends the cocycle
class A_V[z] through H^q(d) to [h(z)], since chain maps respect cycles and boundaries
(def-weil-derived-cohomology-sheaves). Substitute Q(d) = b from Step 3. This is the
stated equality, including degree zero, zero sheaves, identities and empty schemes. -/
theorem siteComparison_edge_section (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
      ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) :
    siteComparisonProEtaleEdge Λ f F q (siteComparisonCohomologyMap U Λ F q x) =
      siteComparisonHigherImageSectionMap Λ f F q (siteComparisonEtaleEdge Λ f F q x) := by
  sorry

end AlgebraicGeometry.ProEtale
