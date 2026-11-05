/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Counit square for affine spectrum pullback composition

Source: Stacks Project, Tag 0D5S.
(blueprint: lem-pc-affine-spectrum-composition-counit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private theorem pushforwardCongr_refl {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforwardCongr (rfl : f = f) = Iso.refl _ := by
  ext M U
  simp

private theorem tensor_composition_inv
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).inv =
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm).hom := by
  unfold Scheme.Modules.tensorPullbackCompositionIso
  rw [pushforwardCongr_refl]
  rfl

private theorem tensor_composition_symm
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).symm =
      (conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm :=
  Iso.ext (tensor_composition_inv f g)

private theorem map_complex_comparison
    {V W D : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
    [Category D] {F G H : V ⥤ W}
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
    (a : F ≅ G) (b : F ≅ H)
    (Q : CochainComplex W ℤ ⥤ D) (P : CochainComplex V ℤ) :
    Q.map ((NatIso.mapHomologicalComplex (a.symm ≪≫ b) (.up ℤ)).hom.app P) =
      (Q.mapIso ((NatIso.mapHomologicalComplex a (.up ℤ)).app P)).inv ≫
        (Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app P)).hom := by
  change Q.map ((NatTrans.mapHomologicalComplex (a.inv ≫ b.hom) (.up ℤ)).app P) = _
  rw [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app, Q.map_comp]
  rfl

private theorem reassoc_factorization
    {C : Type*} [Category C] {U V A B D : C}
    (c : U ≅ V) (ε : V ⟶ A) (l : U ⟶ B) (r : B ⟶ D) (t : D ⟶ A)
    (h : c.hom ≫ 𝟙 V ≫ ε = l ≫ r ≫ t) : c.hom ≫ ε = (l ≫ r) ≫ t := by
  simpa only [Category.id_comp, Category.assoc] using h

private theorem reassoc_transported_factorization
    {C : Type*} [Category C] {U V V' A B D : C}
    (c : U ≅ V) (e : V ≅ V') (ε : V' ⟶ A)
    (l : U ⟶ B) (r : B ⟶ D) (t : D ⟶ A)
    (h : c.hom ≫ e.hom ≫ ε = l ≫ r ≫ t) :
    (c ≪≫ e).hom ≫ ε = (l ≫ r) ≫ t :=
  (Category.assoc c.hom e.hom ε).trans (h.trans (Category.assoc l r t).symm)

private theorem eqToIso_congr_symm
    {C D : Type*} [Category D] (F : C → D) {k l : C} (h : k = l) :
    eqToIso (congrArg F h.symm) = (eqToIso (congrArg F h)).symm := by
  subst l
  rfl

private theorem compare_counit_factorizations
    {C : Type*} [Category C] {U V W A B D : C}
    (c₁ : U ≅ V) (c₂ : W ≅ V) (b₁ : A ≅ B) (b₂ : A ≅ D)
    (ε : V ⟶ A) (l : U ⟶ B) (r : W ⟶ D)
    (h₁ : c₁.hom ≫ ε = l ≫ b₁.inv) (h₂ : c₂.hom ≫ ε = r ≫ b₂.inv) :
    l ≫ b₁.inv ≫ b₂.hom = c₁.hom ≫ c₂.inv ≫ r := by
  have hr : r = c₂.hom ≫ ε ≫ b₂.hom := by
    rw [← Category.assoc, h₂, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hr]
  simp only [Iso.inv_hom_id_assoc]
  exact ((reassoc_of% h₁) b₂.hom).symm

private noncomputable def selectedComposition
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback.{u, w} g ⋙ derivedPullback.{u, w} f ≅ derivedPullback.{u, w} (f ≫ g) :=
  (Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))) f g

end AlgebraicGeometry.SingleComplexBaseChange
