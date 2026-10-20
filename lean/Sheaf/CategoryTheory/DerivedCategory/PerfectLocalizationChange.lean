/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.CategoryTheory.Localization.Predicate

/-! # Perfectness is independent of the chosen derived localization

Source: Stacks Project, Tags 05RU and 09AW.
(blueprint: lem-sfb-perfect-change-derived-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u w₁ w₂
open CategoryTheory
namespace DerivedCategory
/-- Changing the localization universe preserves exactly the same bounded
finite-projective representatives.

Source: Stacks Project, Tags 05RU and 09AW; the uniqueness of localization.
(blueprint: lem-sfb-perfect-change-derived-localization).

Proof: the canonical localization equivalence identifies the image of each actual
cochain complex with its image in the other localization. In the forward direction,
apply its inverse to a bounded finite-projective marking and compose with its unit.
In the reverse direction, apply its functor and its comparison with localization.
The representative, both degree bounds and all finite-projective terms are unchanged. -/
theorem isPerfectRingComplex_change_localization_iff {R : Type u} [CommRing R]
    (h₁ : HasDerivedCategory.{w₁} (ModuleCat.{u} R))
    (h₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} R))
    (K : @DerivedCategory (ModuleCat.{u} R) _ _ h₁) :
    @IsPerfectRingComplex R _ h₂
        ((Localization.uniq
          (@DerivedCategory.Q (ModuleCat.{u} R) _ _ h₁)
          (@DerivedCategory.Q (ModuleCat.{u} R) _ _ h₂)
          (HomologicalComplex.quasiIso _ (.up ℤ))).functor.obj K) ↔
      @IsPerfectRingComplex R _ h₁ K := by
  let Q₁ := @DerivedCategory.Q (ModuleCat.{u} R) _ _ h₁
  let Q₂ := @DerivedCategory.Q (ModuleCat.{u} R) _ _ h₂
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)
  let E := Localization.uniq Q₁ Q₂ W
  constructor
  · rintro ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩
    exact ⟨P, a, b, ha, hb, hP,
      ⟨E.unitIso.app K ≪≫ E.inverse.mapIso e ≪≫
        (Localization.compUniqInverse Q₁ Q₂ W).app P⟩⟩
  · rintro ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩
    exact ⟨P, a, b, ha, hb, hP,
      ⟨E.functor.mapIso e ≪≫ (Localization.compUniqFunctor Q₁ Q₂ W).app P⟩⟩
end DerivedCategory
