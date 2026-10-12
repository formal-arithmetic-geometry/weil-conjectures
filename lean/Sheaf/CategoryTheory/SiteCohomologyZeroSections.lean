/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Evaluation of degree-zero object cohomology
Source: Mathlib, SheafCohomology/Basic, Ext/Basic, Sheafification and Yoneda.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Evaluate a degree-zero Ext class on the identity generator of the free sheaf.
Source: Mathlib, SheafCohomology/Basic, Ext/Basic, Sheafification and Yoneda.
(blueprint: lem-weil-pbc-object-cohomology-zero-evaluation).
-/
noncomputable def siteCohomology_zero_section
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})]
    (A : Sheaf T AddCommGrpCat.{u}) (X : C) (x : Sheaf.H' A 0 X) :
    A.obj.obj (op X) :=
  ((Abelian.Ext.addEquiv₀ x).hom.app (op X)).hom
    (((toSheafify T (yoneda.obj X ⋙ AddCommGrpCat.free)).app (op X)).hom
      (FreeAbelianGroup.of (𝟙 X)))

/-- Degree-zero evaluation is injective, preserves zero, and is natural in the sheaf.
Source: Mathlib, SheafCohomology/Basic, Ext/Basic, Sheafification and Yoneda.
(blueprint: lem-weil-pbc-object-cohomology-zero-evaluation).

Proof: Ext in degree zero is additively equivalent to Hom. The sheafification
adjunction identifies Hom from the free sheaf with natural transformations from
its free representable presheaf. The free-forgetful adjunction then identifies
these with maps from the representable to the underlying presheaf. Yoneda
identifies such maps with sections at X, by evaluation on the identity. All
three identifications preserve zero. Postcomposition with a sheaf morphism
commutes with each identification, proving the displayed naturality equation.
-/
theorem siteCohomology_zero_section_properties
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    [HasSheafify T AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf T AddCommGrpCat.{u})] :
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      Function.Injective (siteCohomology_zero_section T A X)) ∧
    (∀ (A : Sheaf T AddCommGrpCat.{u}) (X : C),
      siteCohomology_zero_section T A X 0 = 0) ∧
    (∀ (A B : Sheaf T AddCommGrpCat.{u}) (f : A ⟶ B) (X : C)
      (x : Sheaf.H' A 0 X),
      siteCohomology_zero_section T B X
          ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
        (f.hom.app (op X)).hom (siteCohomology_zero_section T A X x)) := by
  constructor
  · intro A X x y h
    apply Abelian.Ext.addEquiv₀.injective
    apply ((sheafificationAdjunction T AddCommGrpCat.{u}).homEquiv
      (yoneda.obj X ⋙ AddCommGrpCat.free) A).injective
    apply ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv
      (yoneda.obj X) A.obj).injective
    apply yonedaEquiv.injective
    exact h
  constructor
  · intro A X
    unfold siteCohomology_zero_section
    rw [map_zero]
    rfl
  · intro A B f X x
    have hx : Abelian.Ext.addEquiv₀
        ((((Sheaf.cohomologyPresheafFunctor T 0).map f).app (op X)).hom x) =
        Abelian.Ext.addEquiv₀ x ≫ f := by
      delta Abelian.Ext.addEquiv₀
      apply (Abelian.Ext.mk₀_bijective _ B).injective
      simp only [AddEquiv.coe_mk, Abelian.Ext.mk₀_homEquiv₀_apply,
        ← Abelian.Ext.mk₀_comp_mk₀]
      rfl
    unfold siteCohomology_zero_section
    rw [hx]
    rfl

end CategoryTheory
