/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso

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
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

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

/-- The composition comparison intertwines the successive derived counits at a complex.
There is no coefficient morphism, representative isomorphism or K-flatness assumption.
Source: Stacks Project, Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-pc-affine-spectrum-composition-counit-square).

Proof: Apply the leftDerived_fac_app equation to each of the two chosen composition
comparisons, at the image of P in the homotopy category. Expand whiskering and
associators: each equation is the composite of the two successive counits followed
by Qh of the underived composition comparison. The latter is the inverse of the
pinned tensorPullbackCompositionIso, since conjugation commutes with inversion and
pushforwardCongr rfl is the identity. Transport the second equation along
isoSpec_inv_naturality. Its total pullback and counit agree with those in the first
equation by equality elimination and proof irrelevance. Cancel the second derived
comparison and the first underived comparison. The resulting square is precisely
the displayed equation. The quotient/localization comparison has identity components;
its naturality identifies Qh of the termwise comparison with Q of that comparison.
No inversion of a counit is used; zero complexes and empty schemes satisfy the same
factorization equations. -/
theorem affineSpectrum_composition_counit_square
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} [IsAffine X] [IsAffine X']
    (g' : X' ⟶ X)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let a : Scheme.Modules.tensorPullback X.isoSpec.inv ⋙
        Scheme.Modules.tensorPullback (Spec.map g'.appTop) ≅
        Scheme.Modules.tensorPullback g' ⋙ Scheme.Modules.tensorPullback X'.isoSpec.inv :=
      (Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
      Scheme.Modules.tensorPullbackCompositionIso X'.isoSpec.inv g'
        ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm
    (derivedPullback (Spec.map g'.appTop)).map
        ((counit X.isoSpec.inv).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (counit (Spec.map g'.appTop)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex a (.up ℤ)).hom.app P) =
    (affineSpectrumDerivedPullbackIso g').hom.app (DerivedCategory.Q.obj P) ≫
      (derivedPullback X'.isoSpec.inv).map
        ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (counit X'.isoSpec.inv).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)) := by
  sorry

end AlgebraicGeometry.SingleComplexBaseChange
