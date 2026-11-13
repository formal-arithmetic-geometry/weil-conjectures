/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.DirectImageGlobalSectionsKInjectiveAcyclic

/-! # Affine scalar actions in the derived sections/pushforward comparison

## References

* Stacks Project, Tags 0D5T, 08D5 and 0AA7
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Exact postcomposition retains every object on which the derived unit is invertible. -/
private theorem exactComp_unit_isIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (G : C ⥤ D) (S : D ⥤ E) [G.Additive] [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (J : HomotopyCategory C (.up ℤ))
    (h : IsIso (G.rightDerivedFunctorUnit.app J)) :
    IsIso ((G ⋙ S).rightDerivedFunctorUnit.app J) := by
  have := Functor.isRightDerivedFunctor_rightDerivedFunctor_comp_of_exact G S
  let e := Functor.rightDerivedUnique (G ⋙ S).rightDerivedFunctor
    (G.rightDerivedFunctor ⋙ S.rightDerivedFunctor)
    (G ⋙ S).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit G S)
    (HomotopyCategory.quasiIso C (.up ℤ))
  have he : (G ⋙ S).rightDerivedFunctorUnit.app J ≫
      e.hom.app (DerivedCategory.Qh.obj J) =
      (Functor.rightDerivedFunctorCompUnit G S).app J := by
    simpa only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app (G ⋙ S).rightDerivedFunctor
        (G.rightDerivedFunctor ⋙ S.rightDerivedFunctor)
        (G ⋙ S).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit G S)
        (HomotopyCategory.quasiIso C (.up ℤ)) (𝟙 _) J
  have : IsIso ((Functor.rightDerivedFunctorCompUnit G S).app J) := by
    dsimp [Functor.rightDerivedFunctorCompUnit]
    infer_instance
  have : IsIso ((G ⋙ S).rightDerivedFunctorUnit.app J ≫
      e.hom.app (DerivedCategory.Qh.obj J)) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ (e.hom.app (DerivedCategory.Qh.obj J))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The derived composite is universal when the second unit is invertible on F(I). -/
private theorem composite_isRightDerived_of_acyclic
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (h : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)))) :
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso
      _ (fun J ↦ ?_)
  obtain ⟨I, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective J
  change IsIso ((Functor.rightDerivedFunctorCompUnit F G).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I))
  have h₁ : IsIso (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) := inferInstance
  have h₂ := h I
  dsimp [Functor.rightDerivedFunctorCompUnit]
  infer_instance

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (A : Type u) [Ring A], HasDerivedCategory.{w} (ModuleCat.{u} A)]

set_option maxHeartbeats 500000 in
-- Scalar-action comparisons unfold global-section and derived-functor identifications.
/-- Sections of pushforward retain their affine scalar action before and after deriving
(Stacks, Tags 0D5T, 08D5 and 0AA7). -/
theorem exists_affineSectionsPushforwardNormalization
    {R B : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (g : Spec B ⟶ Spec R) :
    let ρ := ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso B).hom).hom
    let r := ModuleCat.restrictScalars.{u}
      ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
    let b := ModuleCat.restrictScalars.{u}
      ((Scheme.ΓSpecIso B).inv ≫ (pullback.snd f g).appTop).hom
    let G := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ r
    let H := RingedSpace.globalSectionsFunctor (pullback f g).toRingedSpace ⋙ b
    let DG := schemeDerivedGlobalSections X ⋙ r.mapDerivedCategory
    let DH := schemeDerivedGlobalSections (pullback f g) ⋙ b.mapDerivedCategory
    let uG := Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (RingedSpace.globalSectionsFunctor X.toRingedSpace) r
    let uH := Functor.rightDerivedFunctorCompMapDerivedCategoryIso H
        (ModuleCat.restrictScalars.{u} ρ) ≪≫
      Functor.isoWhiskerRight
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
          (RingedSpace.globalSectionsFunctor (pullback f g).toRingedSpace) b)
        (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory
    ∃ (s : RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom ⋙
          G ≅
        H ⋙
          ModuleCat.restrictScalars.{u} ρ)
      (c : schemeDerivedDirectImage (pullback.fst f g) ⋙
          DG ≅
        DH ⋙
          (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory),
      (∀ (F : SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))
          (x : (H).obj F),
        (s.hom.app F) x = x) ∧
      (∀ J : HomotopyCategory
          (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) (ComplexShape.up ℤ),
        (Functor.rightDerivedFunctorCompUnit
            (RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom)
            (G)).app J ≫
          uG.hom.app
            ((schemeDerivedDirectImage (pullback.fst f g)).obj (DerivedCategory.Qh.obj J)) ≫
          c.hom.app (DerivedCategory.Qh.obj J) =
        DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (ComplexShape.up ℤ)).app J) ≫
          (H ⋙
            ModuleCat.restrictScalars.{u} ρ).rightDerivedFunctorUnit.app J ≫
          uH.hom.app (DerivedCategory.Qh.obj J)) := by
  dsimp only
  let α := ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom
  let β := ((Scheme.ΓSpecIso B).inv ≫ (pullback.snd f g).appTop).hom
  let ρ := ((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso B).hom).hom
  let δ := (pullback.fst f g).appTop.hom
  have he : δ.comp α = β.comp ρ := by
    change (((Scheme.ΓSpecIso R).inv ≫ f.appTop) ≫
      (pullback.fst f g).appTop).hom =
      (((Scheme.ΓSpecIso R).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso B).hom) ≫
        ((Scheme.ΓSpecIso B).inv ≫ (pullback.snd f g).appTop)).hom
    congr 1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Scheme.Hom.comp_appTop, pullback.condition, Scheme.Hom.comp_appTop]
  let e := (ModuleCat.restrictScalarsComp α δ).symm ≪≫
    ModuleCat.restrictScalarsComp' ρ β (δ.comp α) he
  let s := Functor.isoWhiskerLeft
    (RingedSpace.globalSectionsFunctor (pullback f g).toRingedSpace) e
  let F := RingedSpace.moduleDirectImage (pullback.fst f g).toLRSHom.toShHom
  let G₀ := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let r := ModuleCat.restrictScalars.{u} α
  let G := G₀ ⋙ r
  let H := RingedSpace.globalSectionsFunctor (pullback f g).toRingedSpace ⋙
    ModuleCat.restrictScalars.{u} β
  let S := ModuleCat.restrictScalars.{u} ρ
  let uG := Functor.rightDerivedFunctorCompMapDerivedCategoryIso G₀ r
  let uH := Functor.rightDerivedFunctorCompMapDerivedCategoryIso H S ≪≫
    Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (RingedSpace.globalSectionsFunctor (pullback f g).toRingedSpace)
        (ModuleCat.restrictScalars.{u} β)) S.mapDerivedCategory
  have hG : ∀ (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) ℤ) [I.IsKInjective],
      IsIso (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) := by
    intro I hI
    exact exactComp_unit_isIso G₀ r _
      (isIso_directImage_globalSections_unit_on_kInjective (pullback.fst f g) I)
  have := composite_isRightDerived_of_acyclic F G hG
  let eD := Functor.rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso _ (.up ℤ))
  let c := Functor.isoWhiskerLeft F.rightDerivedFunctor uG.symm ≪≫
    eD.symm ≪≫ Functor.rightDerivedFunctorNatIso s ≪≫ uH
  refine ⟨s, c, ?_, ?_⟩
  · intro M x
    rfl
  · intro J
    have heD : (F ⋙ G).rightDerivedFunctorUnit.app J ≫
        eD.hom.app (DerivedCategory.Qh.obj J) =
        (Functor.rightDerivedFunctorCompUnit F G).app J := by
      simpa only [eD, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
        Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
        Functor.rightDerivedNatTrans_app (F ⋙ G).rightDerivedFunctor
          (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
          (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
          (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _) J
    have hfac : (Functor.rightDerivedFunctorCompUnit F G).app J ≫
        eD.inv.app (DerivedCategory.Qh.obj J) = (F ⋙ G).rightDerivedFunctorUnit.app J := by
      erw [← heD, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    change (Functor.rightDerivedFunctorCompUnit F G).app J ≫
      uG.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj J)) ≫
        c.hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((s.hom.mapHomotopyCategory (.up ℤ)).app J) ≫
        (H ⋙ S).rightDerivedFunctorUnit.app J ≫ uH.hom.app (DerivedCategory.Qh.obj J)
    simp only [c, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      NatTrans.comp_app, Iso.symm_hom, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hfac]
    dsimp only [Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans]
    rw [Functor.rightDerivedNatTrans_app_assoc]
    rfl

end AlgebraicGeometry
