/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
import all WeilConjectures.ProperBaseChange.RingedKoszulFactorColimit

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
