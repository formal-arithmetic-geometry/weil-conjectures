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
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Tactic.Basic
import WeilConjectures.ProperBaseChange.RingedLocalizationFactorTensorAugmentation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import WeilConjectures.Algebra.Homology.KFlatComparison
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Acyclicity of the extended Cech tensor-augmentation cone

Source: Stacks Project, algebraization.tex, Tag 099B.
(blueprint: lem-weil-pbc-ringed-cech-tensor-idempotence).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory Opposite MonoidalCategory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

section
variable {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
variable (W : MorphismProperty D) [W.IsMultiplicative] [W.RespectsIso]

end

private theorem ringComplex_kflat (O : Sheaf J CommRingCat.{u}) :
    CochainComplex.IsAcyclicTensorKFlat (ringedSiteRingComplex O) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (ne_of_gt hn)
  · intro n
    let := SheafOfModules.monoidalCategory O
    by_cases hn : n = 0
    · subst n
      have h := ObjectProperty.prop_unit
        (ObjectProperty.flat (A := SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))
      exact ((ObjectProperty.flat).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm h).tensorRight
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)).tensorRight

private theorem ringSheaf_flat (O : Sheaf J CommRingCat.{u}) :
    SheafOfModules.IsFlat
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  exact (ObjectProperty.prop_unit (ObjectProperty.flat (A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)))).tensorRight

attribute [local irreducible] ringedSectionLocalization ringedSectionLocalizationPresheaf
  SheafOfModules.monoidalCategory

private theorem localizationFactor_kflat (O : Sheaf J CommRingCat.{u})
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    CochainComplex.IsAcyclicTensorKFlat (ringedLocalizationTwoTerm O s) := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  apply CochainComplex.isKFlat_of_boundedAbove_flat
  · refine ⟨1, fun n hn ↦ ?_⟩
    change IsZero (ringedLocalizationTwoTermX O s n)
    simp only [ringedLocalizationTwoTermX, if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 1 by omega)]
    exact isZero_zero _
  · intro n
    change SheafOfModules.IsFlat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      let := SheafOfModules.monoidalCategory O
      exact ringSheaf_flat O
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact localization_isFlat (C := C) (J := J) O s
      · simp only [ringedLocalizationTwoTermX, if_neg hn, if_neg hn']
        let := SheafOfModules.monoidalCategory O
        exact (ObjectProperty.flat_of_isZero (isZero_zero _)).tensorRight

attribute [local semireducible] SheafOfModules.monoidalCategory
attribute [local instance_reducible] SheafOfModules.monoidalCategory

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

attribute [local irreducible] ringedExtendedCech SheafOfModules.monoidalCategory

end CategoryTheory
