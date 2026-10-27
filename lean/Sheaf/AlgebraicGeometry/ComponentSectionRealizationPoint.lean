/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-! # Point realization comparison for component pullback
Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3)
(blueprint: lem-zl-component-section-realization-point).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
  [PreservesFiniteColimits (componentInverse T)]
private def pointModuleIso
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T)
    (hβ : NatTrans.IsMonoidal β.hom) (hα : α.hom.hom = β.hom.app Λ.X) :
    ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T)).mapMod Λ.X ⋙ componentModules Λ.X T α ≅
      (upperStarFromPoint T).mapMod Λ.X := by
  letI := hβ
  let F := (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
    (affineComponentSpace T)
  let G := componentInverse T
  let H := upperStarFromPoint T
  let e := Functor.mapModCompIso F G β.hom Λ.X
  have hc : α.inv.hom ≫ Functor.compAlgHom F G β.hom Λ.X = 𝟙 _ := by
    rw [Functor.compAlgHom, ← hα]
    exact congrArg Mon.Hom.hom α.inv_hom_id
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e (Mod.comap α.inv.hom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (H.mapMod Λ.X)
      ((Mod.comapComp α.inv.hom (Functor.compAlgHom F G β.hom Λ.X)).symm ≪≫
        Mod.comapCongr hc ≪≫ Mod.comapId _) ≪≫ Functor.rightUnitor _

private def pointDerivedIso
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T)
    (hβ : NatTrans.IsMonoidal β.hom) (hα : α.hom.hom = β.hom.app Λ.X) :
    profiniteScalarRealization Λ.X (affineComponentSpace T) ⋙ componentDerived Λ.X T α ≅
      condensedScalarRealization Λ.X T := by
  let F := ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
    (affineComponentSpace T)).mapMod Λ.X
  let G := componentModules Λ.X T α
  letI : PreservesFiniteLimits (upperStarFromPoint T) := by
    unfold upperStarFromPoint pointUpperStar
    infer_instance
  letI : PreservesFiniteColimits (upperStarFromPoint T) := by
    let := pointUpperStarLowerStarAdjunction.{u}.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let H := (upperStarFromPoint T).mapMod Λ.X
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  letI : H.Additive := Functor.additive_of_preserves_binary_products H
  let e : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (pointModuleIso Λ T α β hβ hα)
  let c := commutativeSiteDerivedConstantModuleFunctor
    (coherentTopology Profinite.{u}) (condensedScalarRing Λ.X)
  let d := (condensedScalarExtensionModel Λ.X).T
  letI := Functor.additive_of_preserves_binary_products
    (InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ.X).inverse
  let E := (InternalAbelianSheafModule.sectionModuleEquivalence
    (coherentTopology Profinite.{u}) Λ.X).inverse.mapDerivedCategory
  exact Functor.associator c (d ⋙ E ⋙ F.mapDerivedCategory) G.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft c
      (Functor.associator d (E ⋙ F.mapDerivedCategory) G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft d
          (Functor.associator E F.mapDerivedCategory G.mapDerivedCategory ≪≫
            Functor.isoWhiskerLeft E e))

/-- The point realization comparison induced by a monoidal component factorization.
Source: Hemo--Richarz--Scholbach, Remark 3.2, Proposition 4.3(3)
(blueprint: lem-zl-component-section-realization-point).
The module comparison is the derived image of the monoidal natural isomorphism β;
its coefficient transport is cancelled using α and the identity
α⁻¹ ∘ α = 1. -/
theorem component_section_realization_point
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T)
    (hβ : NatTrans.IsMonoidal β.hom) (hα : α.hom.hom = β.hom.app Λ.X) :
    Nonempty (profiniteScalarRealization Λ.X (affineComponentSpace T) ⋙
      componentDerived Λ.X T α ≅ condensedScalarRealization Λ.X T) :=
  ⟨pointDerivedIso Λ T α β hβ hα⟩


end AlgebraicGeometry.ProEtale.CondensedRing
