/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantScalarPullbackCube

/-! # Ordinary finite-reduction pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private def conjugate
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {F F' : C ⥤ C'} {G G' : D ⥤ D'} (Q : C ⥤ D) (R : C' ⥤ D')
    (a : F ≅ F') (b : G ≅ G') (e : F ⋙ R ≅ Q ⋙ G) : F' ⋙ R ≅ Q ⋙ G' :=
  Functor.isoWhiskerRight a.symm R ≪≫ e ≪≫ Functor.isoWhiskerLeft Q b
private def paste
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {F : C₀ ⥤ C₁} {H : C₁ ⥤ C₂} {G : D₀ ⥤ D₁} {I : D₁ ⥤ D₂}
    {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂}
    (e : F ⋙ Q₁ ≅ Q₀ ⋙ G) (h : H ⋙ Q₂ ≅ Q₁ ⋙ I) :
    (F ⋙ H) ⋙ Q₂ ≅ Q₀ ⋙ G ⋙ I :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F h ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e I ≪≫
      Functor.associator _ _ _
private def modelPaste
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F F' : C₀ ⥤ C₁} {H H' : C₁ ⥤ C₂} (a : F ≅ F') (b : H ≅ H') :
    F ⋙ H ≅ F' ⋙ H' :=
  Functor.isoWhiskerLeft F b ≪≫ Functor.isoWhiskerRight a H'

private theorem conjugate_square
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {F F' H H' : C ⥤ C'} {G G' I I' : D ⥤ D'}
    (Q : C ⥤ D) (R : C' ⥤ D')
    (a : F ≅ F') (b : H ≅ H') (c : G ≅ G') (d : I ≅ I')
    (e : F ⋙ R ≅ Q ⋙ G) (h : H ⋙ R ≅ Q ⋙ I)
    (s : F ≅ H) (t : G ≅ I)
    (hs : Functor.isoWhiskerRight s R ≪≫ h = e ≪≫ Functor.isoWhiskerLeft Q t) :
    Functor.isoWhiskerRight (a.symm ≪≫ s ≪≫ b) R ≪≫ conjugate Q R b d h =
      conjugate Q R a c e ≪≫ Functor.isoWhiskerLeft Q (c.symm ≪≫ t ≪≫ d) := by
  apply Iso.ext
  ext K
  have hh := congr_app (congrArg Iso.hom hs) K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hh
  simp only [conjugate, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (b.hom.app K) (b.inv.app K), Iso.hom_inv_id_app]
  simp only [R.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% hh]

-- Project an object-isomorphism equality while the isomorphism is still abstract.
open AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] sfIntrinsicModuleEquivalence Functor.mapDerivedCategory
end AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.mapDerivedCategory
-- Expose only the equivalence projections needed in the endpoint types below.
attribute [local implicit_reducible] CategoryTheory.Equivalence.mapDerivedCategory
  CategoryTheory.Equivalence.mk
private lemma derived_inverse_triangle
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (e : C ≌ D) [e.functor.Additive] [e.inverse.Additive]
    (Y : DerivedCategory C) :
    e.functor.mapDerivedCategory.map
        (((Functor.mapDerivedCategoryCompIso e.functor e.inverse).inv.app Y) ≫
          (Functor.mapDerivedCategoryNatIso e.unitIso.symm).hom.app Y ≫
          (Functor.mapDerivedCategoryIdIso C).hom.app Y) =
      (Functor.mapDerivedCategoryCompIso e.inverse e.functor).inv.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app
          (e.functor.mapDerivedCategory.obj Y) ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (e.functor.mapDerivedCategory.obj Y) := by
  have h := Functor.mapDerivedCategoryCompNatIso_cocycle
    e.unitIso.symm (Iso.refl e.functor) e.counitIso (Iso.refl e.functor)
    (fun X ↦ by simpa using (e.counit_app_functor X).symm) Y
  simp only [Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom] at h
  have hl := congr_app (Functor.mapDerivedCategoryCompIso_id_comp e.functor) Y
  have hr := congr_app (Functor.mapDerivedCategoryCompIso_comp_id e.functor) Y
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hl hr
  have hl' : (Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).inv.app Y =
      e.functor.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app Y) := by
    exact ((Iso.hom_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso (𝟭 C) e.functor).app Y)).mp hl).symm
  have hr' : (Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).inv.app Y =
      (Functor.mapDerivedCategoryIdIso D).hom.app
        (e.functor.mapDerivedCategory.obj Y) := by
    exact ((Iso.hom_comp_eq_id
      ((Functor.mapDerivedCategoryCompIso e.functor (𝟭 D)).app Y)).mp hr).symm
  rw [hl', hr'] at h
  apply (cancel_mono ((Functor.mapDerivedCategoryNatIso (Iso.refl e.functor)).hom.app Y)).mp
  simpa only [Functor.map_comp, Category.assoc] using h

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
section
variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [Abelian C] [Abelian D] [Abelian E] [Abelian H]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory H]
  (F : C ⥤ D) (G : D ⥤ E) (J : E ⥤ H)
  [F.Additive] [G.Additive] [J.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits J] [PreservesFiniteColimits J]
end
section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F F' : C ⥤ D} {G G' : D ⥤ E}
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
end

attribute [local irreducible] Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso
section
variable {S C D E T J : Type*}
  [Category S] [Category C] [Category D] [Category E] [Category T] [Category J]
  [Abelian S] [Abelian C] [Abelian D] [Abelian E] [Abelian T] [Abelian J]
  [HasDerivedCategory S] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory T] [HasDerivedCategory J]
  (A : S ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (B : E ⥤ T) (e : D ≌ J)
  [A.Additive] [F.Additive] [G.Additive] [B.Additive]
  [e.functor.Additive] [e.inverse.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
end

section
variable {S C D E : Type*} [Category S] [Category C] [Category D] [Category E]
  [Abelian S] [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory S] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E]
  (A : S ⥤ C) (F G : C ⥤ D) (B : D ⥤ E)
  [A.Additive] [F.Additive] [G.Additive] [B.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
end

namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Scheme.sfIntrinsicTransport Scheme.sfIntrinsicPullback
  Scheme.sfIntrinsicDerivedEquivalence Coefficient coefficientCommRing
  smoothPurityPullback finiteReductionPullback
end WeilConjectures.PurityFiniteSetting

namespace AlgebraicGeometry.Scheme
end AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] Scheme.sfIntrinsicDerivedEquivalence
private def modelSquare (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : ChosenCartesianSquare u f' f v) :
    P.finiteReductionPullback f ⋙ P.finiteReductionPullback u ≅
      P.finiteReductionPullback v ⋙ P.finiteReductionPullback f' :=
  (modelPaste (P.finiteReductionRawPullbackModel f)
    (P.finiteReductionRawPullbackModel u)).symm ≪≫
    (ProEtale.directImageConstantPullbackIso P.Ring sq).symm ≪≫
    modelPaste (P.finiteReductionRawPullbackModel v)
      (P.finiteReductionRawPullbackModel f')
end WeilConjectures.PurityFiniteSetting
