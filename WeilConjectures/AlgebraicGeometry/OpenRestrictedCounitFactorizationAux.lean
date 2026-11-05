/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedTensorComplexIso
public import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonComposition
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

private abbrev schemeModulesDerived
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) : HasDerivedCategory.{w} Y.Modules := d Y

attribute [local instance] schemeModulesDerived

private theorem open_restriction_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    (openRestrictionRepresentativeIso j P).hom ≫
        (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (openTensorRestrictionIso j).symm (.up ℤ)).hom.app P) := by
  classical
  let T := Scheme.Modules.tensorPullback j
  have : T.Additive := tensorPullbackAdditive.{u, w} j
  let R := openRestrictionFunctor j
  let θ : T ≅ R := openTensorRestrictionIso j
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ.symm
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ.symm
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback j).IsLeftDerivedFunctor (counit j) W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) j
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let e := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback j) (counit j)
    T.mapDerivedCategoryFactorsh.hom W
  have he : e.inv.app (DerivedCategory.Q.obj P) ≫
      (counit j).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      T.mapDerivedCategoryFactors.hom.app P := by
    have h := Functor.leftDerivedNatTrans_app T.mapDerivedCategory (derivedPullback j)
      T.mapDerivedCategoryFactorsh.hom (counit j) W (𝟙 _)
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    simp only [NatTrans.id_app, Category.comp_id] at h
    change e.inv.app (DerivedCategory.Q.obj P) ≫ _ = _ at h
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
    change e.inv.app (DerivedCategory.Q.obj P) ≫ _ =
      T.mapDerivedCategory.map (𝟙 _) ≫ T.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) at h
    erw [T.mapDerivedCategory.map_id,
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map_id] at h
    erw [Category.id_comp, Category.comp_id] at h
    exact h.trans (Category.comp_id _)
  change (R.mapDerivedCategoryFactors.inv.app P ≫
    (Functor.mapDerivedCategoryNatIso θ).inv.app (DerivedCategory.Q.obj P) ≫
      e.inv.app (DerivedCategory.Q.obj P)) ≫ _ = _
  rw [Category.assoc, Category.assoc, he]
  have hn := Functor.mapDerivedCategoryNatIso_fac θ.symm P
  change (Functor.mapDerivedCategoryNatIso θ).inv.app (DerivedCategory.Q.obj P) ≫
    T.mapDerivedCategoryFactors.hom.app P = _ at hn
  rw [hn]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem tensor_square_inverse
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (k : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    ((Scheme.Modules.tensorPullback (pullback.snd k U.ι)).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex (openTensorRestrictionIso U.ι) (.up ℤ)).inv.app P) ≫
      ((NatIso.mapHomologicalComplex
        (Scheme.Modules.tensorPullbackCompositionIso (pullback.snd k U.ι) U.ι
          (pullback.fst k U.ι ≫ k) pullback.condition.symm) (.up ℤ)).app P).inv ≫
      ((NatIso.mapHomologicalComplex
        (Scheme.Modules.tensorPullbackCompositionIso (pullback.fst k U.ι) k
          (pullback.fst k U.ι ≫ k) rfl) (.up ℤ)).app P).hom ≫
      (NatIso.mapHomologicalComplex (openTensorRestrictionIso (pullback.fst k U.ι))
        (.up ℤ)).hom.app
        (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj P) =
      (openTensorRestrictionComplexIso k U P).inv := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [openTensorRestrictionComplexIso, openTensorRestrictionSquareIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]
  rfl

private theorem restriction_counit_glue
    {V : Type*} [Category V] {A B C D E F G H I J : V}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (e : D ⟶ E) (t : E ⟶ F)
    (f : B ⟶ G) (g : G ⟶ H) (i : H ⟶ I) (j : I ⟶ E)
    (v : A ⟶ G) (l : A ⟶ J) (m : J ⟶ H) (n : J ⟶ F) (d : D ≅ F)
    (hc : b ≫ c ≫ e = f ≫ g ≫ i ≫ j) (ha : a ≫ f = v)
    (hn : v ≫ g = l ≫ m) (hd : e ≫ t = d.hom) (ht : m ≫ i ≫ j ≫ t = n) :
    a ≫ b ≫ c = l ≫ n ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hd, reassoc_of% hc, reassoc_of% ha, reassoc_of% hn, ht]

private theorem counit_iso_inverse
    {V : Type*} [Category V] {A B C : V} (e : A ≅ B) (t : C ≅ A) (ε : B ⟶ C)
    (h : e.hom ≫ ε = t.inv) : ε ≫ t.hom = e.inv := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, h]
  simp only [Iso.inv_hom_id, Iso.hom_inv_id]

attribute [local implicit_reducible] Scheme.Modules TopCat.Sheaf

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] openRestrictionRepresentativeIso openRestrictedCompositionMap
  openRestrictedTensorDerivedIso openTensorRestrictionComplexIso openTensorRestrictionSquareIso
  openTensorRestrictionIso counit

end AlgebraicGeometry.SingleComplexBaseChange
