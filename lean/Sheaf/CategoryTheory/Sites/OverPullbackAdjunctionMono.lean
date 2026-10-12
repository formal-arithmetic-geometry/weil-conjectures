/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf

/-!
# Extension by zero for an arbitrary localized Grothendieck topology

Source: Stacks Project, Modules on Sites, Lemmas 03DI and 03DJ
(blueprint: new-over-pullback-adjunction-mono).

The presheaf hom-equivalence and injectivity arguments adapt the private helpers of
`SiteExtensionByZeroPresheafAdjoint` and `SiteExtensionByZeroExact`. Sheafification
then gives the result without the precoverage or pullback assumptions of those modules.
-/

@[expose] public section

universe u

namespace CategoryTheory

private abbrev sliceRestrict {C : Type u} [SmallCategory C] (W : C) :=
  (Functor.whiskeringLeft (Over W)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj (Over.forget W).op

private noncomputable def sumLift {C : Type u} [SmallCategory C] (W : C)
    {F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F ⟶ (sliceRestrict W).obj G) :
    (siteExtensionByZeroPresheaf W).obj F ⟶ G := by
  classical
  exact {
    app V := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ ↦
      (α.app (Opposite.op (Over.mk φ))).hom)
    naturality V V' a := by
      classical
      apply AddCommGrpCat.hom_ext
      dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
        siteExtensionByZeroRestrict, siteExtensionByZeroSection]
      apply DirectSum.addHom_ext
      intro φ x
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      exact ConcreteCategory.congr_hom (α.naturality
        (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))) x }

private noncomputable def sumRestrict {C : Type u} [SmallCategory C] (W : C)
    {F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (β : (siteExtensionByZeroPresheaf W).obj F ⟶ G) :
    F ⟶ (sliceRestrict W).obj G := by
  classical
  exact {
    app Y := AddCommGrpCat.ofHom
      (DirectSum.of (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
        Y.unop.hom) ≫ β.app (Opposite.op Y.unop.left)
    naturality Y Y' a := by
      classical
      apply AddCommGrpCat.hom_ext
      ext x
      have h := ConcreteCategory.congr_hom (β.naturality ((Over.forget W).op.map a))
        (DirectSum.of (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
          Y.unop.hom x)
      dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
        siteExtensionByZeroRestrict, siteExtensionByZeroSection] at h
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of] at h
      have aux (j : Y'.unop.left ⟶ W) (hj : j = Y'.unop.hom)
          (f : Over.mk j ⟶ Y.unop) (hf : f.left = a.unop.left) :
          DirectSum.of (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) j
            ((F.map f.op).hom x) =
          DirectSum.of (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) Y'.unop.hom
            ((F.map a).hom x) := by
        subst j
        have he : f = a.unop := Over.OverMorphism.ext hf
        subst f
        rfl
      have aux' := aux (a.unop.left ≫ Y.unop.hom) (Over.w a.unop)
        (Over.homMk a.unop.left : Over.mk (a.unop.left ≫ Y.unop.hom) ⟶ Y.unop) rfl
      erw [aux'] at h
      exact h }

private noncomputable def sumHomEquiv {C : Type u} [SmallCategory C] (W : C)
    (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((siteExtensionByZeroPresheaf W).obj F ⟶ G) ≃
      (F ⟶ (sliceRestrict W).obj G) where
  toFun := sumRestrict W
  invFun := sumLift W
  left_inv β := by
    classical
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro φ x
    simp [sumLift, sumRestrict]
  right_inv α := by
    classical
    apply NatTrans.ext
    funext Y
    apply AddCommGrpCat.hom_ext
    ext x
    dsimp [sumLift, sumRestrict]
    erw [DirectSum.toAddMonoid_of]
    rfl

private noncomputable def sumAdjunction {C : Type u} [SmallCategory C] (W : C) :
    siteExtensionByZeroPresheaf W ⊣ sliceRestrict W :=
  Adjunction.mkOfHomEquiv {
    homEquiv := sumHomEquiv W
    homEquiv_naturality_left_symm := by
      intro F' F G α β
      classical
      apply NatTrans.ext
      funext V
      apply AddCommGrpCat.hom_ext
      apply DirectSum.addHom_ext
      intro φ x
      dsimp [sumHomEquiv, sumLift, siteExtensionByZeroPresheaf, siteExtensionByZeroHom,
        siteExtensionByZeroHomApp]
      erw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      erw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
    homEquiv_naturality_right := by
      intro F G G' α β
      apply NatTrans.ext
      funext Y
      simp [sumHomEquiv, sumRestrict, sliceRestrict, Category.assoc] }

/-- Extension by zero along `Over.forget W` exists on abelian sheaves and preserves
monomorphisms.  It is obtained by sheafifying the sectionwise direct-sum extension;
see Stacks Project, Lemmas 03DI--03DJ.
(blueprint: new-over-pullback-adjunction-mono)
-/
theorem overPullback_extensionByZero
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    (W : C) [HasSheafify (J.over W) AddCommGrpCat.{u}] :
    ∃ (L : Sheaf (J.over W) AddCommGrpCat.{u} ⥤ Sheaf J AddCommGrpCat.{u}),
      Nonempty (L ⊣ J.overPullback AddCommGrpCat.{u} W) ∧ L.PreservesMonomorphisms := by
  let P := siteExtensionByZeroPresheaf.{u, u, u} W
  let L := sheafToPresheaf (J.over W) AddCommGrpCat.{u} ⋙ P ⋙
    presheafToSheaf J AddCommGrpCat.{u}
  have hP : P.PreservesMonomorphisms := by
    constructor
    intro X Y α hα
    classical
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro V
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    change Function.Injective (siteExtensionByZeroHomApp W α V).hom
    have hmap : (siteExtensionByZeroHomApp W α V).hom =
        DirectSum.map (fun φ : V.unop ⟶ W =>
          (α.app (Opposite.op (Over.mk φ))).hom) := by
      apply DirectSum.addHom_ext
      intro φ x
      dsimp [siteExtensionByZeroHomApp, siteExtensionByZeroSection]
      simp only [DirectSum.toAddMonoid_of, DirectSum.map_of, AddMonoidHom.comp_apply]
    rw [hmap]
    apply (DirectSum.map_injective _).mpr
    intro φ
    exact (AddCommGrpCat.mono_iff_injective _).mp (inferInstance)
  have hL : L.PreservesMonomorphisms := inferInstance
  let adj : L ⊣ J.overPullback AddCommGrpCat.{u} W :=
    ((sumAdjunction W).comp (sheafificationAdjunction J AddCommGrpCat.{u})).restrictFullyFaithful
      (fullyFaithfulSheafToPresheaf (J.over W) AddCommGrpCat.{u})
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  exact ⟨L, ⟨adj⟩, hL⟩

end CategoryTheory
