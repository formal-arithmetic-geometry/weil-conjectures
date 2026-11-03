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
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
-- Terminal comparison comes from the normalized finite-coefficient public import.
-- The full proof-only operations and CohomologicalDimension imports bring duplicate Iso modules.


/-! # The canonical comparison mate and the Leray identifications

Source: the restriction identity and its adjunction mate in the opening paragraph of
relative Kummer transport (blueprint: lem-pur-site-comparison-leray-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.EdgeComparison

/-- The underived terminal-sections identification on the etale site. -/
def etaleSectionsComp (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    Etale.lowerStar (ModuleCat.{u + 1} Λ) f ⋙ siteComparisonEtaleSections V Λ ≅
      siteComparisonEtaleSections U Λ :=
  Functor.isoWhiskerLeft _
    ((Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ)
      (Scheme.Etale.isTerminalMkId V)) ≪≫ sheafSectionsNatIsoEvaluation _ _).symm ≪≫
    Etale.lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f ≪≫
    Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ) (Scheme.Etale.isTerminalMkId U) ≪≫
    sheafSectionsNatIsoEvaluation _ _

/-- The underived terminal-sections identification on the pro-etale site. -/
def proEtaleSectionsComp (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStar (ModuleCat.{u + 1} Λ) f ⋙ siteComparisonProEtaleSections V Λ ≅
      siteComparisonProEtaleSections U Λ :=
  Functor.isoWhiskerLeft _
    ((Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ)
      (Scheme.ProEt.isTerminalMkId V)) ≪≫ sheafSectionsNatIsoEvaluation _ _).symm ≪≫
    ProEtale.globalSectionsLowerStarIso (ModuleCat.{u + 1} Λ) f ≪≫
    Sheaf.ΓNatIsoSheafSections _ (ModuleCat.{u + 1} Λ) (Scheme.ProEt.isTerminalMkId U) ≪≫
    sheafSectionsNatIsoEvaluation _ _

end AlgebraicGeometry.ProEtale.EdgeComparison

namespace AlgebraicGeometry.ProEtale

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
    (EdgeComparison.etaleSectionsComp Λ f)

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
    (EdgeComparison.proEtaleSectionsComp Λ f)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.EdgeComparison

/-- The unit-normalized global comparison commutes with the Leray identifications
and the specified direct-image mate.
Source: restriction transpose and adjunction-mate normalization in relative Kummer
transport (blueprint: lem-pur-site-comparison-leray-mate).

Proof:
1. Let e_U and e_V be the comparison units evaluated at the terminal objects,
and a_f the underived comparison mate. The adjunction mate unit equation is
η_V(f_*F) followed by ν_V,* a_f = f_*(η_U(F)) followed by the inverse restriction
comparison `f_* ν_U,* ≅ ν_V,* f_*`. It is exactly
`unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app`.
2. Evaluate this identity at the terminal etale object of V. Use the canonical
pullback-terminal identifications to identify the two sides with
`etaleSectionsComp.inv ≫ e_V ≫ proEtaleSections.map a_f` and
`e_U ≫ proEtaleSectionsComp.inv`. The auxiliary global-sections isomorphisms in
the etale Leray construction use two terminal objects. Their composite is the
restriction map along the unique arrow between those objects: expand
`Sheaf.ΓNatIsoSheafSections`, use `Adjunction.rightAdjointUniq_trans_app`, and
compute the constant-presheaf counit as restriction. The resulting restriction
arrows agree by terminal uniqueness. Thus this evaluation is the required
underived pasted-square identity, with its specified normalizations.
3. Both direct-image functors preserve injectives, since their left adjoints are
exact. Apply `rightDerivedFunctorPlusBaseChange_comp` to the underived square
from Step 2. Its two composition isomorphisms are exactly the two displayed
Leray identifications, and its direct-image comparison is
`fixedComparisonDirectImageMatePlus` by definition.
4. Precompose the resulting identity with the inverse canonical derived-identity
isomorphism. Its naturality moves this inverse across the etale Leray map.
This is the displayed identity, with both global comparisons normalized. -/
theorem leray_mate (Λ : Type (u + 1)) [CommRing Λ]
    {U V : Scheme.{u}} (f : U ⟶ V)
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    letI := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
        ((siteComparisonEtaleSections U Λ).rightDerivedFunctorPlus.obj K) ≫
      (finiteComparisonGlobalSections U Λ).app K ≫
      (siteComparisonProEtaleLerayIso Λ f).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategoryPlus.obj K) =
    (siteComparisonEtaleLerayIso Λ f).inv.app K ≫
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} Λ)).inv.app
        ((siteComparisonEtaleSections V Λ).rightDerivedFunctorPlus.obj
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K)) ≫
      (finiteComparisonGlobalSections V Λ).app
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K) ≫
      (siteComparisonProEtaleSections V Λ).rightDerivedFunctorPlus.map
        ((fixedComparisonDirectImageMatePlus Λ f).app K) := by sorry

end AlgebraicGeometry.ProEtale.EdgeComparison
