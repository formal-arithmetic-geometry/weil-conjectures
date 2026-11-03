/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import all WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingCore
import WeilConjectures.SixFunctors.AdicQbarRealization.Reindexing.AdicReindexingComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionDerivedIdentityUnit
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry
set_option linter.style.haveILetI false
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

private theorem identity_of_composition {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) (G : B ⥤ B) (R : A ⥤ B)
    (e : F ≅ 𝟭 A) (b : G ≅ 𝟭 B) (a : F ⋙ R ≅ R ⋙ G)
    (M : A) (c : F.obj M ⟶ F.obj (F.obj M))
    (d : G.obj (R.obj M) ⟶ G.obj (G.obj (R.obj M)))
    (hc : c ≫ e.hom.app (F.obj M) = 𝟙 _)
    (hd : d ≫ b.hom.app (G.obj (R.obj M)) = 𝟙 _)
    (hcomp : a.hom.app M ≫ d =
      R.map c ≫ a.hom.app (F.obj M) ≫ G.map (a.hom.app M)) :
    a.hom.app M ≫ b.hom.app (R.obj M) = R.map (e.hom.app M) := by
  let q : F ⋙ R ≅ R := a ≪≫ Functor.isoWhiskerLeft R b ≪≫ Functor.rightUnitor R
  have hq (N : A) : q.hom.app N = a.hom.app N ≫ b.hom.app (R.obj N) := by
    simp only [q, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    erw [Category.comp_id]
  have h1 : R.map c ≫ q.hom.app (F.obj M) = 𝟙 _ := by
    apply (cancel_mono (a.hom.app M)).1
    have h := congrArg (fun f ↦ f ≫ b.hom.app (G.obj (R.obj M))) hcomp
    simp only [Category.assoc] at h
    rw [hd] at h
    erw [Category.comp_id] at h
    have hb := b.hom.naturality (a.hom.app M)
    dsimp only [Functor.comp_obj, Functor.id_map] at hb
    erw [hb] at h
    simpa only [hq, Category.assoc, Category.id_comp, Functor.id_map] using h.symm
  have hc_eq : c = inv (e.hom.app (F.obj M)) := by
    apply (cancel_mono (e.hom.app (F.obj M))).1
    rw [hc, IsIso.inv_hom_id]
  haveI : IsIso c := by rw [hc_eq]; infer_instance
  have h2 : q.hom.app (F.obj M) = R.map (e.hom.app (F.obj M)) := by
    apply (cancel_epi (R.map c)).1
    rw [h1, ← R.map_comp, hc, R.map_id]
  have he : F.map (e.hom.app M) = e.hom.app (F.obj M) := by
    apply (cancel_mono (e.hom.app M)).1
    exact e.hom.naturality (e.hom.app M)
  have hn := q.hom.naturality (e.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [he, h2] at hn
  apply (cancel_epi (R.map (e.hom.app (F.obj M)))).1
  simpa only [hq, Category.assoc, Functor.id_obj] using hn

private theorem derived_identity_unit {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (F : A ⥤ A) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    (e : F ≅ 𝟭 A) (c : F ≅ F ⋙ F)
    (hc : ∀ M, c.hom.app M ≫ e.hom.app (F.obj M) = 𝟙 _) (K : DerivedCategory A) :
    (Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso F F).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A).hom.app
        (F.mapDerivedCategory.obj K) = 𝟙 _ := by
  have ha (M : A) : c.inv.app M = F.map (e.hom.app M) := by
    apply (cancel_epi (c.hom.app M)).1
    rw [Iso.hom_inv_id_app]
    have he : F.map (e.hom.app M) = e.hom.app (F.obj M) := by
      apply (cancel_mono (e.hom.app M)).1
      exact e.hom.naturality (e.hom.app M)
    rw [he, hc]
  let d := Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso F F
  let b := Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso A
  have hi : d.inv.app K = F.mapDerivedCategory.map (b.hom.app K) := by
    have h := exactRestrictionDerivedIdentityUnit F F e c.symm ha K
    simpa only [d, b, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
      Functor.mapDerivedCategoryNatIso_symm] using h
  have hb : b.hom.app (F.mapDerivedCategory.obj K) =
      F.mapDerivedCategory.map (b.hom.app K) := by
    apply (cancel_mono (b.hom.app K)).1
    exact (b.hom.naturality (b.hom.app K)).symm
  change d.hom.app K ≫ b.hom.app (F.mapDerivedCategory.obj K) = 𝟙 _
  rw [hb, ← hi]
  exact d.hom_inv_id_app K

/-- Identity part of normalized reindexing functoriality.
Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 07A4 and 099N.
This is one conjunct of the parent theorem. (blueprint: lem-sf-adic-reindexing-functoriality-id)
-/
theorem normalized_reindexing_identity
(C : FamilyCore l D)
    (h_moduleId_sections : ∀ (T : GeometricSpace D) (M : modules l T.base.left (C.data
      T).realization)
          (U : T.base.left.ProEtᵒᵖ)
          (x : ((modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))).obj M).val.obj U),
        HEq (((C.moduleId T).hom.app M).val.app U x) x)
    (h_integral_normalization : ∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
          (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    (h_sourceId_unit : ∀ (T : GeometricSpace D)
          (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
        letI := (C.data T).units
        HEq
          ((pullbackTensorCommonComposition l (PadicAlgCl l)
              (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
            (C.sourceId T).hom.app
              ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
          (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))) :
    (∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (C.data T).units
    (C.comparison T T (Iso.refl _)).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleId T) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((ordinary l T.base.left (C.data T).realization).obj M) =
    (ordinary l T.base.left (C.data T).realization).map ((C.sourceId T).hom.app M)) := by
  let C' : FamilyCore l D := { C with
    moduleComp := fun T U V g h ↦ normalizedModuleComp l D T U V g h
      (C.data T).realization (C.data U).realization (C.data V).realization
      (C.ring T V (g ≪≫ h)) (C.ring T U g) (C.ring U V h) }
  have hs := fun T U V g h ↦ normalizedModuleComp_sections l D T U V g h
    (C.data T).realization (C.data U).realization (C.data V).realization
    (C.ring T V (g ≪≫ h)) (C.ring T U g) (C.ring U V h)
  intro T M
  letI := (C.data T).units
  let F := modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))
  let c : F ≅ F ⋙ F := C'.moduleComp T T T (Iso.refl _) (Iso.refl _)
  have hc (N : modules l T.base.left (C.data T).realization) :
      c.hom.app N ≫ (C.moduleId T).hom.app (F.obj N) = 𝟙 _ := by
    ext U x
    exact eq_of_heq ((h_moduleId_sections T (F.obj N) U
      (((c.hom.app N).val.app U) x)).trans (hs T T T (Iso.refl _) (Iso.refl _) N U x))
  have hd := derived_identity_unit F (C.moduleId T) c hc
    ((ordinary l T.base.left (C.data T).realization).obj M)
  have hcomp := normalized_reindexing_composition l D C' hs h_integral_normalization
    T T T (Iso.refl _) (Iso.refl _) M
  exact identity_of_composition
    (commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left))
    (derivedPull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _)))
    (ordinary l T.base.left (C.data T).realization)
    (C.sourceId T)
    (Functor.mapDerivedCategoryNatIso (C.moduleId T) ≪≫ Functor.mapDerivedCategoryIdIso _)
    (C.comparison T T (Iso.refl _)) M
    (pullbackTensorCommonComposition l (PadicAlgCl l) (𝟙 T.base.left) (𝟙 T.base.left) M).hom
    ((Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso F F).hom.app
      ((ordinary l T.base.left (C.data T).realization).obj M))
    (eq_of_heq (h_sourceId_unit T M)) hd hcomp

end WeilConjectures.AdicQbarRealization
