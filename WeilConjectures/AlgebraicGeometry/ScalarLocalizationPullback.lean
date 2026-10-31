/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import all Mathlib.Algebra.Category.ModuleCat.Colimits
import all Mathlib.Algebra.Module.LocalizedModule.Basic
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-! # Localization and an additive left adjoint

Source: Stacks Project, Modules on Sites, Tag 03EL, and the rank-one colimit
presentation of localization (Tag 00E6).
(blueprint: lem-weil-pbc-scalar-localization-pullback).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A left adjoint which intertwines the two scalar multiplications preserves the
corresponding section localization and its unit map.

Source: Stacks Project, Modules on Sites, Tag 03EL; Algebra, Tag 00E6.
(blueprint: lem-weil-pbc-scalar-localization-pullback).

Proof: write each localization as the colimit of the sequence of rank-one modules
with transition multiplication by its section. The scalar equation makes the chosen
rank-one isomorphism an isomorphism of these diagrams. The left adjoint preserves the
first colimit; uniqueness of colimits then gives the localization isomorphism. Its
stage-zero identity is the required unit identity. The existing cocone is indexed so
that its leg at zero is the fraction map with denominator the first power; compose
that identity with multiplication by the section to recover the localization unit.
This works for zero sections, nilpotents, zero divisors, and the zero ring. -/
theorem scalar_localization_pullback
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.IsLeftAdjoint]
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (b : (R.obj ⋙ forget CommRingCat).sections)
    (c : (S.obj ⋙ forget CommRingCat).sections)
    (hscalar : F.map (ringedKoszulScalar R b) ≫ v.hom =
      v.hom ≫ ringedKoszulScalar S c) :
    ∃ loc : F.obj (ringedSectionLocalization R b) ≅ ringedSectionLocalization S c,
      F.map (ringedSectionLocalizationUnit R b) ≫ loc.hom =
        v.hom ≫ ringedSectionLocalizationUnit S c := by
  let d := localizationSheafCocone S c
  let A := Functor.ofSequence (X := fun _ : ℕ ↦
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (fun _ ↦ ringedKoszulScalar R b)
  let B := Functor.ofSequence (X := fun _ : ℕ ↦
    SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
      (fun _ ↦ ringedKoszulScalar S c)
  let τ : A ⋙ F ⟶ B := NatTrans.ofSequence (fun _ ↦ v.hom) (by
    intro n
    simpa only [A, B, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      using hscalar)
  let e : A ⋙ F ≅ B := NatIso.ofComponents (fun _ ↦ v) (fun f ↦ τ.naturality f)
  let hc := isColimitOfPreserves F (localizationSheafCoconeIsColimit R b)
  let hd := (IsColimit.precomposeHomEquiv e d).symm
    (localizationSheafCoconeIsColimit S c)
  let loc := hc.coconePointUniqueUpToIso hd
  refine ⟨loc, ?_⟩
  have hleg : F.map (localizationSheafMap R b 1) ≫ loc.hom =
      v.hom ≫ localizationSheafMap S c 1 :=
    hc.comp_coconePointUniqueUpToIso_hom hd 0
  have hsrc : ringedKoszulScalar R b ≫ localizationSheafMap R b 1 =
      ringedSectionLocalizationUnit R b := by
    rw [localizationSheafMap_step, localizationSheafMap_zero]
  have htgt : ringedKoszulScalar S c ≫ localizationSheafMap S c 1 =
      ringedSectionLocalizationUnit S c := by
    rw [localizationSheafMap_step, localizationSheafMap_zero]
  rw [← hsrc, F.map_comp, Category.assoc, hleg, ← Category.assoc, hscalar,
    Category.assoc, htgt]

end CategoryTheory
