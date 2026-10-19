/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.CategoryTheory.SheafPullbackUnitPresentation
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Sheaf.CategoryTheory.ModuleInverseImageUnitComparison
/-! # Underlying abelian inverse image for finite noncommutative coefficients

Source: Stacks Project, Tags 00YV, 03D2 and 03D3.
(blueprint: lem-exc-proetale-finite-module-underlying).

The private model-site comparisons adapt the commutative-ring construction of
`ProEtaleModelRingPresentation` to RingCat and retain the actual adjunction unit.
-/
@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace AlgebraicGeometry.Scheme
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable def modelRingUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R ⟶
    ((proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
        RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
          ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)) :=
  ⟨Functor.whiskerLeft AsSmall.down.op
    ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩
private noncomputable def modelSheafEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) RingCat.{u + 1} ≌
      Sheaf (ProEt.topology X) RingCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelRingAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (modelSheafEquivalence Y).functor ⋙ proEtaleSheafInverseImage f RingCat.{u + 1} ⋙
      (modelSheafEquivalence X).inverse ⊣
        (proEtaleModelBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
  (proEtaleSheafAdjunction f RingCat.{u + 1}).restrictFullyFaithful
    (modelSheafEquivalence Y).fullyFaithfulFunctor
    (modelSheafEquivalence X).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
private theorem modelRingAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    (modelRingAdjunction f).unit.app ((modelSheafEquivalence Y).inverse.obj R) =
      ⟨CategoryTheory.Functor.whiskerLeft AsSmall.down.op
        ((proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom⟩ := by
  apply (modelSheafEquivalence Y).functor.map_injective
  rw [modelRingAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl
/-- The actual transported ring unit is a set inverse-image unit.
Source: Stacks Project, Tags 09A5, 00YV and 03D2.
(blueprint: lem-weil-pbc-proetale-model-ring-presentation).
Proof: transport the original ring adjunction through the strict
AsSmall equivalences. Its unit is the stated ring unit on sections. Compare this
left adjoint with the model ring pullback, respecting units. Forgetting
rings commutes with filtered Kan extension and sheafification, and its canonical
comparison respects units too. Compose the two comparisons. -/
private theorem modelRingPresentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) RingCat.{u + 1}) :
    let A := ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj R
    let B := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      RingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
        ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
    ∃ p : SheafPullbackUnitPresentation (F := proEtaleModelBaseChange f)
      ((sheafCompose (proEtaleModelTopology Y) (CategoryTheory.forget RingCat.{u + 1})).obj A)
      ((sheafCompose (proEtaleModelTopology X) (CategoryTheory.forget RingCat.{u + 1})).obj B),
      ∀ U r, p.unit.hom.app U r = (modelRingUnit f R).hom.app U r := by
  let F := proEtaleModelBaseChange f
  let J := proEtaleModelTopology Y
  let K := proEtaleModelTopology X
  let A := (modelSheafEquivalence Y).inverse.obj R
  let B := (modelSheafEquivalence X).inverse.obj
    ((proEtaleSheafInverseImage f RingCat.{u + 1}).obj R)
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits F := by
    dsimp [F, proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat F := flat_of_preservesFiniteLimits F
  let e := (modelRingAdjunction f).leftAdjointUniq
    (sheafAdjunctionContinuous F RingCat.{u + 1} J K)
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget RingCat.{u + 1})
  let iso : (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).obj B ≅
      (sheafPullback F (Type (u + 1)) J K).obj
        ((sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).obj A) :=
    (sheafCompose K (CategoryTheory.forget RingCat.{u + 1})).mapIso (e.app A) ≪≫
      c.app A
  let unit :=
    (sheafCompose J (CategoryTheory.forget RingCat.{u + 1})).map (modelRingUnit f R)
  refine ⟨⟨unit, iso, ?_⟩, fun U r ↦ rfl⟩
  intro U r
  have he := Adjunction.unit_leftAdjointUniq_hom_app (modelRingAdjunction f)
    (sheafAdjunctionContinuous F RingCat.{u + 1} J K) A
  have hc := sheafPullbackForgetIso_unit J K F (CategoryTheory.forget RingCat.{u + 1}) A
  have ht := modelRingAdjunction_unit f R
  have ht' := congrArg (fun z ↦ z.hom.app U) ht
  have htr : ((modelRingAdjunction f).unit.app A).hom.app U r = unit.hom.app U r :=
    ConcreteCategory.congr_hom ht' r
  have he' := congrArg (fun z ↦ z.hom.app U) he
  have he0 := ConcreteCategory.congr_hom he' r
  have hc' := congrArg (fun z ↦ z.hom.app U) hc
  have hc0 := ConcreteCategory.congr_hom hc' r
  change (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) (unit.hom.app U r)) = _
  exact (congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U)
      ((e.hom.app A).hom.app (F.op.obj U) t)) htr.symm).trans
    ((congrArg (fun t ↦ (c.hom.app A).hom.app (F.op.obj U) t) he0).trans hc0)
private noncomputable def modelAbelianEquivalence (X : Scheme.{u}) :
    Sheaf (proEtaleModelTopology X) AddCommGrpCat.{u + 1} ≌
      Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)
@[irreducible] private noncomputable def modelAbelianAdjunction {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (modelAbelianEquivalence X).functor ⋙
      proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} ⋙
      (modelAbelianEquivalence Y).inverse ⊣
    (proEtaleModelBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).restrictFullyFaithful
    (modelAbelianEquivalence X).fullyFaithfulFunctor
    (modelAbelianEquivalence Y).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)
private theorem modelAbelianAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}) :
    (modelAbelianAdjunction f).unit.app ((modelAbelianEquivalence Y).inverse.obj N) =
      ⟨Functor.whiskerLeft AsSmall.down.op
        ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app N).hom⟩ := by
  apply (modelAbelianEquivalence Y).functor.map_injective
  rw [modelAbelianAdjunction, Adjunction.map_restrictFullyFaithful_unit_app]
  simp only [Iso.refl_hom, NatTrans.id_app]
  rfl
private noncomputable def modelAbelianPullbackIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) :
    (modelAbelianEquivalence X).inverse ⋙
      Functor.sheafPullbackConstruction.sheafPullback (proEtaleModelBaseChange f)
        AddCommGrpCat.{u + 1} (proEtaleModelTopology X) (proEtaleModelTopology Y) ⋙
      (modelAbelianEquivalence Y).functor ≅
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} := by
  let a := modelAbelianAdjunction f
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology X) (proEtaleModelTopology Y)
  exact Functor.isoWhiskerLeft (modelAbelianEquivalence X).inverse
    (Functor.isoWhiskerRight (b.leftAdjointUniq a) (modelAbelianEquivalence Y).functor)
set_option backward.defeqAttrib.useBackward false in
private noncomputable def toModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleToModel A ⋙
      SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
          (proEtaleModelTopology X) (ProEt.topology X)).obj A) ≅
    SheafOfModules.toSheaf A ⋙ (modelAbelianEquivalence X).inverse :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

set_option backward.defeqAttrib.useBackward false in
private noncomputable def fromModelForgetIso (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    proEtaleModuleFromModel A ⋙ SheafOfModules.toSheaf A ≅
    SheafOfModules.toSheaf
      (((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous RingCat.{u + 1}
        (proEtaleModelTopology X) (ProEt.topology X)).obj A) ⋙
      (modelAbelianEquivalence X).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro M N g
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

open Scheme CategoryTheory.Functor.sheafPullbackConstruction

/-- The constructed finite-ring module inverse image, with its unit, forgets to abelian
inverse image. Source: Stacks Project, Tags 03D2 and 03D3.
(blueprint: lem-exc-proetale-finite-module-underlying).
Proof: present the model ring unit by set inverse image, lift the scalar action through
finite products, and apply the module/abelian unit comparison. Transport the comparison
back through AsSmall; uniqueness of abelian left adjoints preserves the unit. Restriction
along the inverse coefficient isomorphism changes only the action. -/
theorem finiteCoefficientModuleUnderlying_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y) (C : Type (u + 1))
    [Ring C] [Finite C] [TopologicalSpace C] [DiscreteTopology C] :
    ∃ e : finiteCoefficientModulePullback f C ⋙
        SheafOfModules.toSheaf (finiteCoefficientRingSheaf X C) ≅
      SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y C) ⋙
        proEtaleSheafInverseImage f AddCommGrpCat.{u + 1},
      ∀ (N : FiniteCoefficientModules Y C) (W : Y.ProEtᵒᵖ) (m : N.val.obj W),
        (e.hom.app N).hom.app ((proEtaleBaseChange f).op.obj W)
          ((((SheafOfModules.pullbackPushforwardAdjunction
            (finiteCoefficientModelRingUnit f C)).unit.app
            ((proEtaleModuleToModel (finiteCoefficientRingSheaf Y C)).obj N)).val.app
              (AsSmall.up.op.obj W)) m) =
        ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
          ((SheafOfModules.toSheaf (finiteCoefficientRingSheaf Y C)).obj N)).hom.app W m := by
  let : (AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange f) := by
    change PreservesFiniteLimits
      ((AsSmall.down : proEtaleSiteModel Y ⥤ Y.ProEt) ⋙ proEtaleBaseChange f ⋙ AsSmall.up)
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange f) := flat_of_preservesFiniteLimits _
  obtain ⟨pr, hp⟩ := modelRingPresentation f (finiteCoefficientRingSheaf Y C)
  obtain ⟨em, hm⟩ := SheafOfModules.inverseImage_underlying_unit_of_ring_presentation
    (finiteCoefficientModelRingUnit f C) pr (by ext U r; exact hp U r)
  let A := finiteCoefficientRingSheaf Y C
  let B := finiteCoefficientInverseRing f C
  let L := SheafOfModules.pullback (finiteCoefficientModelRingUnit f C)
  let La := sheafPullback (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
    (proEtaleModelTopology Y) (proEtaleModelTopology X)
  let p := Functor.isoWhiskerLeft (proEtaleModuleToModel A ⋙ L) (fromModelForgetIso X B)
  let s := Functor.isoWhiskerLeft (proEtaleModuleToModel A)
    (Functor.isoWhiskerRight em (modelAbelianEquivalence X).functor)
  let t := Functor.isoWhiskerRight (toModelForgetIso Y A)
    (La ⋙ (modelAbelianEquivalence X).functor)
  let e : finiteCoefficientModulePullback f C ⋙
      SheafOfModules.toSheaf (finiteCoefficientRingSheaf X C) ≅
    SheafOfModules.toSheaf A ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1} :=
    p ≪≫ s ≪≫ t ≪≫ Functor.isoWhiskerLeft (SheafOfModules.toSheaf A)
      (modelAbelianPullbackIso f)
  refine ⟨e, ?_⟩
  intro N W m
  have hm' := congrArg (fun q ↦ q.hom.app (AsSmall.up.op.obj W) m)
    (hm ((proEtaleModuleToModel A).obj N))
  have hq := Adjunction.unit_leftAdjointUniq_hom_app
    (sheafAdjunctionContinuous (proEtaleModelBaseChange f) AddCommGrpCat.{u + 1}
      (proEtaleModelTopology Y) (proEtaleModelTopology X))
    (modelAbelianAdjunction f) ((SheafOfModules.toSheaf _).obj
      ((proEtaleModuleToModel A).obj N))
  have hq' := congrArg (fun q ↦ q.hom.app (AsSmall.up.op.obj W) m) hq
  change _ = ((modelAbelianAdjunction f).unit.app
    ((modelAbelianEquivalence Y).inverse.obj ((SheafOfModules.toSheaf A).obj N))).hom.app
      (AsSmall.up.op.obj W) m at hq'
  rw [modelAbelianAdjunction_unit] at hq'
  change ((modelAbelianPullbackIso f).hom.app ((SheafOfModules.toSheaf A).obj N)).hom.app
    ((proEtaleBaseChange f).op.obj W)
      ((La.map (𝟙 _)).hom.app ((proEtaleModelBaseChange f).op.obj (AsSmall.up.op.obj W))
        ((em.hom.app ((proEtaleModuleToModel A).obj N)).hom.app
          ((proEtaleModelBaseChange f).op.obj (AsSmall.up.op.obj W))
            ((((SheafOfModules.pullbackPushforwardAdjunction
              (finiteCoefficientModelRingUnit f C)).unit.app
                ((proEtaleModuleToModel A).obj N)).val.app (AsSmall.up.op.obj W)) m))) = _
  rw [La.map_id]
  exact (congrArg (fun z ↦
    ((modelAbelianPullbackIso f).hom.app ((SheafOfModules.toSheaf A).obj N)).hom.app
      ((proEtaleBaseChange f).op.obj W) z) hm').trans hq'

end AlgebraicGeometry.ProEtale
