/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientPullbackIso
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-!
# The site comparison pullbacks and composition

The identifications `g^* ν_X^* ≅ ν_Y^* g^*` of `comparisonUpperStarCompUpperStarIso` are
compatible with the composition isomorphisms of the étale and pro-étale pullbacks
(`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso_inv_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Functor Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem site_restriction_hom
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T : Scheme.{u}} (f : S ⟶ T) (N : Sheaf (ProEt.topology S) A)
    (V : T.Etaleᵒᵖ) :
    ((lowerStarCompComparisonLowerStarIso f A).hom.app N).hom.app V = 𝟙 _ := by
  change 𝟙 _ ≫ N.obj.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem etale_map_op
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T : Scheme.{u}} (f : S ⟶ T) {N N' : Sheaf S.smallEtaleTopology A}
    (φ : N ⟶ N') (V : T.Etaleᵒᵖ) :
    ((Etale.lowerStar A f).map φ).hom.app V =
      φ.hom.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj V) := rfl

private theorem comparison_map
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (T : Scheme.{u}) {N N' : Sheaf (ProEt.topology T) A} (φ : N ⟶ N') (V : T.Etaleᵒᵖ) :
    ((comparisonLowerStar A T).map φ).hom.app V = φ.hom.app ((toProEt T).op.obj V) := rfl

private theorem comparison_obj_map
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    (T : Scheme.{u}) (N : Sheaf (ProEt.topology T) A) {V W : T.Etaleᵒᵖ} (φ : V ⟶ W) :
    ((comparisonLowerStar A T).obj N).obj.map φ = N.obj.map ((toProEt T).op.map φ) := rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] lowerStarCompComparisonLowerStarIso
  Etale.lowerStarComp ProEtale.lowerStarComp

private theorem site_restriction_comp
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : Sheaf (ProEt.topology S) A) :
    (lowerStarCompComparisonLowerStarIso g A).hom.app ((ProEtale.lowerStar A f).obj N) ≫
      (Etale.lowerStar A g).map ((lowerStarCompComparisonLowerStarIso f A).hom.app N) ≫
      (Etale.lowerStarComp A f g).hom.app ((comparisonLowerStar A S).obj N) =
    (comparisonLowerStar A U).map ((ProEtale.lowerStarComp A f g).hom.app N) ≫
      (lowerStarCompComparisonLowerStarIso (f ≫ g) A).hom.app N := by
  ext V
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    etale_map_op, comparison_map, site_restriction_hom]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [Etale.lowerStarComp_hom_app_hom_app, comparison_obj_map,
    ProEtale.lowerStarComp_hom_app_hom_app]
  congr 1

/-- The site comparison pullbacks commute with the composition isomorphisms of the étale and
pro-étale pullbacks.
Proof: conjugate the composition identity of the comparison direct images. -/
theorem comparisonUpperStarCompUpperStarIso_inv_comp
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A]
    {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U)
    (N : Sheaf U.smallEtaleTopology A) :
    (comparisonUpperStar A S).map ((Etale.upperStarComp A f g).hom.app N) ≫
      (comparisonUpperStarCompUpperStarIso A f).inv.app ((Etale.upperStar A g).obj N) ≫
      (ProEtale.upperStar A f).map ((comparisonUpperStarCompUpperStarIso A g).inv.app N) =
    (comparisonUpperStarCompUpperStarIso A (f ≫ g)).inv.app N ≫
      (ProEtale.upperStarComp A f g).hom.app ((comparisonUpperStar A U).obj N) := by
  let r := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦ lowerStarCompComparisonLowerStarIso h A
  let p := fun {X Y : Scheme.{u}} (h : X ⟶ Y) ↦ comparisonUpperStarCompUpperStarIso A h
  have hp {X Y : Scheme.{u}} (h : X ⟶ Y) :
      conjugateIsoEquiv
        ((Etale.upperStarLowerStarAdjunction A h).comp (comparisonAdjunction A X))
        ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A h))
        (p h) = (r h).symm := by
    unfold p comparisonUpperStarCompUpperStarIso
    exact (conjugateIsoEquiv _ _).apply_symm_apply _
  have hr : r (f ≫ g) =
      isoWhiskerRight (ProEtale.lowerStarComp A f g).symm (comparisonLowerStar A U) ≪≫
      associator (ProEtale.lowerStar A f) (ProEtale.lowerStar A g)
        (comparisonLowerStar A U) ≪≫
      isoWhiskerLeft (ProEtale.lowerStar A f) (r g) ≪≫
      (associator (ProEtale.lowerStar A f) (comparisonLowerStar A T)
        (Etale.lowerStar A g)).symm ≪≫
      isoWhiskerRight (r f) (Etale.lowerStar A g) ≪≫
      associator (comparisonLowerStar A S) (Etale.lowerStar A f) (Etale.lowerStar A g) ≪≫
      isoWhiskerLeft (comparisonLowerStar A S) (Etale.lowerStarComp A f g) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app,
      associator_hom_app, associator_inv_app, Category.id_comp]
    rw [← cancel_epi ((comparisonLowerStar A U).map
      ((ProEtale.lowerStarComp A f g).hom.app M))]
    rw [← (comparisonLowerStar A U).map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (site_restriction_comp A f g M).symm
  have hκ : conjugateIsoEquiv (ProEtale.upperStarLowerStarAdjunction A (f ≫ g))
      ((ProEtale.upperStarLowerStarAdjunction A g).comp
        (ProEtale.upperStarLowerStarAdjunction A f))
      (ProEtale.upperStarComp A f g).symm = (ProEtale.lowerStarComp A f g).symm := by
    rw [conjugateIsoEquiv_iso_symm, ProEtale.conjugateIsoEquiv_upperStarComp]
  have H := adjunctionSquareComposition
    (comparisonAdjunction A U) (comparisonAdjunction A T) (comparisonAdjunction A S)
    (Etale.upperStarLowerStarAdjunction A g) (Etale.upperStarLowerStarAdjunction A f)
    (Etale.upperStarLowerStarAdjunction A (f ≫ g))
    (ProEtale.upperStarLowerStarAdjunction A g) (ProEtale.upperStarLowerStarAdjunction A f)
    (ProEtale.upperStarLowerStarAdjunction A (f ≫ g))
    (r g) (r f) (r (f ≫ g)) (Etale.lowerStarComp A f g).symm
    (ProEtale.lowerStarComp A f g) (p g) (p f) (p (f ≫ g))
    (Etale.upperStarComp A f g) (ProEtale.upperStarComp A f g).symm
    (hp g) (hp f) (hp (f ≫ g)) (Etale.conjugateIsoEquiv_upperStarComp A f g) hκ hr
  have H := congrArg (fun t ↦ t.inv.app N) H
  simp only [Iso.trans_inv, Iso.symm_inv, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    whiskerRight_app, whiskerLeft_app, associator_inv_app, associator_hom_app,
    NatTrans.comp_app, Category.id_comp, Category.comp_id, Category.assoc] at H
  rw [H, ← (comparisonUpperStar A S).map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false

open MonoidalCategory in
/-- The composition isomorphism of derived pullbacks, evaluated on a sheaf placed in degree zero,
is the underived composition isomorphism placed in degree zero, through the single-degree
comparisons. -/
theorem leftDerivedUpperStarComp_hom_app_singleFunctor (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R) (F : Sheaf (ProEt.topology R) A) :
    (leftDerivedUpperStarComp A g₁ g₂).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (ProEtale.upperStar A g₁).leftDerivedFunctor.map
        ((singleFunctorCompLeftDerivedUpperStarIso A g₂).hom.app F) ≫
      (singleFunctorCompLeftDerivedUpperStarIso A g₁).hom.app
        ((ProEtale.upperStar A g₂).obj F) =
    (singleFunctorCompLeftDerivedUpperStarIso A (g₁ ≫ g₂)).hom.app F ≫
      (DerivedCategory.singleFunctor _ 0).map ((ProEtale.upperStarComp A g₁ g₂).hom.app F) := by
  dsimp only [leftDerivedUpperStarComp, singleFunctorCompLeftDerivedUpperStarIso,
    Iso.trans_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj,
    Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj]

end AlgebraicGeometry.ProEtale
