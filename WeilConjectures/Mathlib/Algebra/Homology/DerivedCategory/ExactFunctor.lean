/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# An exact functor induces a functor on bounded below derived categories

This is the bounded below counterpart of
`Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`: an exact functor
`F : C₁ ⥤ C₂` between abelian categories induces a functor
`F.mapDerivedCategoryPlus : DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂`.

Since `DerivedCategory.Plus.Qh` is a localization functor for the quasi-isomorphisms of
`HomotopyCategory.Plus C₁`, the functor is obtained by lifting
`F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh` through it; what has to be checked is
that this composition inverts quasi-isomorphisms, and that follows from the unbounded
`CategoryTheory.Functor.mapDerivedCategory`.

This material is destined for
`Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`, next to
`CategoryTheory.Functor.mapDerivedCategory`.

## Main definitions

- `CategoryTheory.Functor.mapDerivedCategoryPlus`: the functor
  `DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` induced by an exact functor.
- `CategoryTheory.Functor.mapDerivedCategoryPlusFactorsh`: the isomorphism
  `Qh ⋙ F.mapDerivedCategoryPlus ≅ F.mapHomotopyCategoryPlus ⋙ Qh` expressing that
  `F.mapDerivedCategoryPlus` is induced by `F.mapHomotopyCategoryPlus`.

-/

@[expose] public section

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor preserves quasi-isomorphisms of cochain complexes, as a statement about
the homotopy categories. It is the unbounded functor `F.mapDerivedCategory` read through the
characterization of quasi-isomorphisms as the morphisms inverted by `DerivedCategory.Qh`. -/
lemma quasiIso_mapHomotopyCategory_map {K L : HomotopyCategory C₁ (ComplexShape.up ℤ)}
    (f : K ⟶ L) (hf : HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ) f) :
    HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map f) := by
  haveI : IsIso (DerivedCategory.Qh.map f) := (DerivedCategory.isIso_Qh_map_iff f).2 hf
  rw [← DerivedCategory.isIso_Qh_map_iff]
  change IsIso ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map f)
  rw [← NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh f]
  change IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map f))
  infer_instance

/-- The bounded below version of `CategoryTheory.Functor.quasiIso_mapHomotopyCategory_map`:
an exact functor preserves quasi-isomorphisms of bounded below complexes. -/
lemma quasiIso_mapHomotopyCategoryPlus_map {K L : HomotopyCategory.Plus C₁} (f : K ⟶ L)
    (hf : HomotopyCategory.Plus.quasiIso C₁ f) :
    HomotopyCategory.Plus.quasiIso C₂ (F.mapHomotopyCategoryPlus.map f) :=
  F.quasiIso_mapHomotopyCategory_map f.hom hf

/-- For an exact `F`, the composition `F.mapHomotopyCategoryPlus ⋙ Qh` inverts
quasi-isomorphisms, so it factors through the localization `Qh`. -/
lemma isInvertedBy_mapHomotopyCategoryPlus_comp_Qh :
    (HomotopyCategory.Plus.quasiIso C₁).IsInvertedBy
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) := fun _ _ f hf =>
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₂) _
    (F.quasiIso_mapHomotopyCategoryPlus_map f hf)

/-- The functor `DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂` induced by an exact
functor `F : C₁ ⥤ C₂` between abelian categories. Unlike a right derived functor it needs no
injectives: it is `F` applied termwise. -/
noncomputable def mapDerivedCategoryPlus :
    DerivedCategory.Plus C₁ ⥤ DerivedCategory.Plus C₂ :=
  Localization.lift _ F.isInvertedBy_mapHomotopyCategoryPlus_comp_Qh DerivedCategory.Plus.Qh

noncomputable instance :
    Localization.Lifting DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₁)
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.mapDerivedCategoryPlus :=
  Localization.liftingLift _ _ _

/-- The functor `F.mapDerivedCategoryPlus` is induced by `F.mapHomotopyCategoryPlus`. -/
noncomputable def mapDerivedCategoryPlusFactorsh :
    DerivedCategory.Plus.Qh ⋙ F.mapDerivedCategoryPlus ≅
      F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh :=
  Localization.Lifting.iso DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C₁) _ _

end CategoryTheory.Functor
