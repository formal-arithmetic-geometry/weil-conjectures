/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RingedModelCurrying

/-! # Natural currying for localization complexes

Source: Stacks Project, Tags 08J9, 0A90, 0A96 and 0996.
(blueprint: lem-weil-pbc-ringed-localization-natural-currying).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.LocalizationRHom

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

set_option backward.isDefEq.respectTransparency true in
/-- The components of the shared evaluation-normalized model comparison.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-natural-currying). -/
def curryIso (U : C) (f : R.obj.obj (op U))
    (P : CochainComplex (localizationModules R) ℤ) (hP : IsBoundedLocalizationComplex R P)
    (N : localizationDerived R) :
    (localizationRHom (R.over U)).obj
      (op (localizationSliceDerivedCoefficient R U f),
        (localizationRHom (R.over U)).obj
          (op ((localizationDerivedRestriction R U).obj ((localizationQ R).obj P)),
            (localizationDerivedRestriction R U).obj N)) ≅
    (localizationRHom (R.over U)).obj
      (op ((localizationQ (R.over U)).obj ((localizationSliceComplex R U f).obj P)),
        (localizationDerivedRestriction R U).obj N) :=
  modelCurryIso R U (localizationSliceCoefficient R U f)
    (localizationSliceCoefficient_kflat R U f) P
    (ringedLocalization_kflat_models R P hP U f).1 N

set_option maxHeartbeats 400000 in
-- Naturality expands the paired functor maps, but not their derived-Hom bodies.
set_option backward.isDefEq.respectTransparency true in
/-- Simultaneous naturality in a chain map of localization complexes and an arbitrary
derived target morphism. No boundedness of the target is assumed.
Source: Stacks 08J9 (blueprint: lem-weil-pbc-ringed-localization-natural-currying).
Proof: Apply the naturality of the shared model comparison to the supplied
K-flat certificates; these are available for every bounded localization complex. -/
theorem curryIso_natural (U : C) (f : R.obj.obj (op U))
    (P P' : CochainComplex (localizationModules R) ℤ)
    (hP : IsBoundedLocalizationComplex R P) (hP' : IsBoundedLocalizationComplex R P')
    (a : P' ⟶ P) (N N' : localizationDerived R) (b : N ⟶ N') :
    (curryIso R U f P hP N).hom ≫ (localizationRHom (R.over U)).map
      (((localizationQ (R.over U)).map ((localizationSliceComplex R U f).map a)).op,
        (localizationDerivedRestriction R U).map b) =
    (localizationRHom (R.over U)).map
      (𝟙 (op (localizationSliceDerivedCoefficient R U f)),
        (localizationRHom (R.over U)).map
          (((localizationDerivedRestriction R U).map ((localizationQ R).map a)).op,
            (localizationDerivedRestriction R U).map b)) ≫
      (curryIso R U f P' hP' N').hom := by
  exact modelCurryIso_natural R U (localizationSliceCoefficient R U f)
    (localizationSliceCoefficient_kflat R U f) P P'
    (ringedLocalization_kflat_models R P hP U f).1
    (ringedLocalization_kflat_models R P' hP' U f).1 a N N' b

/-- The natural comparison has the evaluation-normalized component formula.
Source: Stacks 08J9 and 0A90
(blueprint: lem-weil-pbc-ringed-localization-natural-currying).
Proof: The localization comparison is defined as the corresponding component
of the shared model comparison; this equality is definitional. -/
theorem curryIso_eq_model (U : C) (f : R.obj.obj (op U))
    (P : CochainComplex (localizationModules R) ℤ) (hP : IsBoundedLocalizationComplex R P)
    (N : localizationDerived R) :
    curryIso R U f P hP N = modelCurryIso R U (localizationSliceCoefficient R U f)
      (localizationSliceCoefficient_kflat R U f) P
      (ringedLocalization_kflat_models R P hP U f).1 N := by
  rfl

end CategoryTheory.LocalizationRHom
