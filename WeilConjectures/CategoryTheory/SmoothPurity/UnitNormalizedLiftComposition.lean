/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-! # Composition of unit-normalized lifts

Source: the formal adjunction calculation in blueprint Steps 15--16 of
`def-pur-condensed-compact-support-projection`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
open CategoryTheory

namespace CategoryTheory

private theorem restriction_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {T : D ⥤ A} {V : A ⥤ D}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ac : T ⊣ V)
    (U : A ⥤ C) (U' : B ⥤ C) (U'' : D ⥤ C)
    (α : U' ≅ P ⋙ U) (β : U'' ≅ Q ⋙ U') (gamma : U'' ≅ T ⋙ U)
    (τ : T ≅ Q ⋙ P)
    (hc : ∀ N, β.hom.app N ≫ α.hom.app (Q.obj N) =
      gamma.hom.app N ≫ U.map (τ.hom.app N)) (M : A) :
    U''.map ((conjugateEquiv (aq.comp ap) ac τ.hom).app M) ≫
        gamma.hom.app (V.obj M) ≫ U.map (ac.counit.app M) =
      β.hom.app (S.obj (R.obj M)) ≫ U'.map (aq.counit.app (R.obj M)) ≫
        α.hom.app (R.obj M) ≫ U.map (ap.counit.app M) := by
  rw [← Category.assoc, gamma.hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← U.map_comp, conjugateEquiv_counit]
  simp only [Adjunction.comp_counit_app, Functor.map_comp]
  rw [← Category.assoc (gamma.hom.app _), ← hc]
  simp only [Category.assoc]
  have hn := α.hom.naturality (aq.counit.app (R.obj M))
  change U'.map (aq.counit.app (R.obj M)) ≫ α.hom.app (R.obj M) =
    α.hom.app (Q.obj (S.obj (R.obj M))) ≫ U.map (P.map (aq.counit.app (R.obj M))) at hn
  rw [reassoc_of% hn]
  rfl

private theorem normalized_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : B ⥤ A} {R : A ⥤ B} {Q : D ⥤ B} {S : B ⥤ D}
    {T : D ⥤ A} {V : A ⥤ D}
    (ap : P ⊣ R) (aq : Q ⊣ S) (ac : T ⊣ V)
    (U : A ⥤ C) (U' : B ⥤ C) (U'' : D ⥤ C)
    (α : U' ≅ P ⋙ U) (β : U'' ≅ Q ⋙ U') (gamma : U'' ≅ T ⋙ U)
    (τ : T ≅ Q ⋙ P)
    (hc : ∀ N, β.hom.app N ≫ α.hom.app (Q.obj N) =
      gamma.hom.app N ≫ U.map (τ.hom.app N))
    {K : C} {M : A} {N : B} {O : D}
    (x : K ⟶ U'.obj N) (y : K ⟶ U''.obj O) (z : K ⟶ U.obj M)
    (u : N ⟶ R.obj M) (v : O ⟶ S.obj N)
    (hu : x ≫ U'.map u ≫ α.hom.app (R.obj M) ≫
      U.map (ap.counit.app M) = z)
    (hv : y ≫ U''.map v ≫ β.hom.app (S.obj N) ≫
      U'.map (aq.counit.app N) = x) :
    y ≫ U''.map (v ≫ S.map u ≫
      (conjugateEquiv (aq.comp ap) ac τ.hom).app M) ≫
      gamma.hom.app (V.obj M) ≫ U.map (ac.counit.app M) = z := by
  simp only [Functor.map_comp, Category.assoc]
  rw [restriction_comp ap aq ac U U' U'' α β gamma τ hc M]
  rw [β.hom.naturality_assoc]
  simp only [Functor.comp_map]
  have hn := aq.counit.naturality u
  change Q.map (S.map u) ≫ aq.counit.app (R.obj M) = aq.counit.app N ≫ u at hn
  rw [← U'.map_comp_assoc, hn, U'.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hv]
  exact hu

end CategoryTheory
