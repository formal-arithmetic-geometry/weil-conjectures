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
public import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Ordinary tensor evaluation for ringed-site complexes

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08JJ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

attribute [local irreducible] homComplexFunctor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

local instance : MonoidalPreadditive (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  (SheafOfModules.tensorClosed O).1.some

local instance : HasColimitsOfSize.{0, 0} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  hasColimitsOfSizeShrink.{0, 0, u, u} _

attribute [local instance] ringedComplexClosed

section Generic

variable {D : Type v} [Category.{w} D] [MonoidalCategory D]
  [MonoidalClosed D] [BraidedCategory D]

private theorem evaluation_naturality (P : D) {N M : D} (f : N ⟶ M) :
    f ▷ ((ihom P).obj (𝟙_ D)) ≫ (β_ M _).hom ≫
        MonoidalClosed.ihomUnitTensorToIhom P M =
      (β_ N _).hom ≫ MonoidalClosed.ihomUnitTensorToIhom P N ≫ (ihom P).map f := by
  rw [BraidedCategory.braiding_naturality_left_assoc]
  congr 1
  dsimp only [MonoidalClosed.ihomUnitTensorToIhom]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_right]
  congr 1
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc]
  dsimp only [Functor.id_obj]
  rw [leftUnitor_naturality]

private theorem evaluation_unit (N : D) :
    (ρ_ N).inv ≫ N ◁ MonoidalClosed.unitNatIso.hom.app (𝟙_ D) ≫
        (β_ N _).hom ≫ MonoidalClosed.ihomUnitTensorToIhom (𝟙_ D) N =
      MonoidalClosed.unitNatIso.hom.app N := by
  rw [BraidedCategory.braiding_naturality_right_assoc]
  dsimp only [MonoidalClosed.ihomUnitTensorToIhom]
  rw [← MonoidalClosed.curry_natural_left, ← MonoidalClosed.curry_natural_left,
    ← MonoidalClosed.curry_natural_left, MonoidalClosed.unitNatIso_hom_app N]
  congr 1
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    MonoidalClosed.whiskerLeft_unitNatIso_hom_app_ihom_ev_app,
    braiding_tensorUnit_right]
  monoidal

end Generic

end CategoryTheory
