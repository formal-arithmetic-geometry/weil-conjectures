/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import all WeilConjectures.AlgebraicGeometry.ProEtale.Scalar.ProEtaleScalarTensorBalance

/-! # Cancelling the identity coefficient factor in ordinary inverse image

Source: Stacks Tags 03D2 and 03EK; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-identity-cancellation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

private theorem scalarIdentity (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ e : pbcExtend (𝟙 A) ≅ 𝟭 (pbcModules X A),
      ∀ (M : pbcModules X A) (W : X.ProEtᵒᵖ) (m : M.val.obj W),
        (e.hom.app M).val.app W (pbcTensorSection (𝟙 A) M W 1 m) = m := by
  let r : pbcRestrict (𝟙 A) ≅ 𝟭 (pbcModules X A) := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun W ↦ Iso.refl _) (by intros; rfl)
    · intro M N f
      ext W m
      rfl
  let a := (pbcScalarAdjunction (𝟙 A)).ofNatIsoRight r
  let e := a.leftAdjointUniq Adjunction.id
  refine ⟨e, ?_⟩
  intro M W m
  have h := congrArg (fun f ↦ f.val.app W m)
    (a.unit_leftAdjointUniq_hom_app Adjunction.id M)
  change (e.hom.app M).val.app W
    (((pbcScalarAdjunction (𝟙 A)).unit.app M).val.app W m) = m at h
  have hu := (pbcScalarAdjunction_exists (𝟙 A)).exists.choose_spec M W m
  change (((pbcScalarAdjunction (𝟙 A)).unit.app M).val.app W m) = _ at hu
  rw [hu] at h
  exact h

set_option maxHeartbeats 2400000 in
-- The comparison includes several sheafification and coefficient transports.
/-- Remove the identity scalar extension inserted by the exact ringed inverse-image
API. The comparison fixes every sheafified tensor generator.
Source: Stacks Tags 03D2 and 03EK; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-identity-cancellation).

Proof: restriction along the identity coefficient map is naturally the identity on
sections. Its normalized scalar-extension left adjoint is therefore uniquely isomorphic
to the identity functor. The adjunction-unit equation says that this isomorphism takes
one tensor m to m. The recorded object and map equalities for ordinary scalar extension
identify the identity extension in ringed inverse image with this functor. Whisker the
result with extension along c. Naturality of the scalar unit proves the desired formula
for coefficient one; linearity proves it for every coefficient s. These calculations
are valid for zero rings and empty site objects as well. -/
theorem nativePullbackIdentityCancellation {X Y : Scheme.{u}} (p : X ⟶ Y)
    {A : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (adicTowerInverseImage p).obj A ⟶ B) :
    ∃ e : proEtaleRingModulePullback p A ((adicTowerInverseImage p).obj A) (Iso.refl _) ⋙
        pbcExtend c ≅ ContinuousRational.modulePull p c,
      ∀ (M : pbcModules Y A) (W : X.ProEtᵒᵖ) (s : B.obj.obj W)
        (m : ((proEtaleModuleInverseImage p A).obj M).val.obj W),
      (e.hom.app M).val.app W
        (pbcTensorSection c
          ((proEtaleRingModulePullback p A ((adicTowerInverseImage p).obj A)
            (Iso.refl _)).obj M) W s
          ((eqToHom ((completedAdicChangeData
            X (𝟙 ((adicTowerInverseImage p).obj A))).choose_spec.choose
              ((proEtaleModuleInverseImage p A).obj M))).val.app W
              (pbcTensorSection (𝟙 ((adicTowerInverseImage p).obj A))
                ((proEtaleModuleInverseImage p A).obj M) W 1 m))) =
        pbcTensorSection c ((proEtaleModuleInverseImage p A).obj M) W s m := by
  let A' := (adicTowerInverseImage p).obj A
  let F := proEtaleModuleInverseImage p A
  let G := proEtaleRingModulePullback p A A' (Iso.refl _)
  let h (M : pbcModules Y A) : (pbcExtend (𝟙 A')).obj (F.obj M) = G.obj M :=
    (completedAdicChangeData X (𝟙 A')).choose_spec.choose (F.obj M)
  let k : G ≅ F ⋙ pbcExtend (𝟙 A') := NatIso.ofComponents
    (fun M ↦ eqToIso (h M).symm) (by
      intro M N f
      have hm : (pbcExtend (𝟙 A')).map (F.map f) =
          eqToHom (h M) ≫ G.map f ≫ eqToHom (h N).symm :=
        (completedAdicChangeData X (𝟙 A')).choose_spec.choose_spec.choose (F.map f)
      change G.map f ≫ eqToHom (h N).symm =
        eqToHom (h M).symm ≫ (pbcExtend (𝟙 A')).map (F.map f)
      apply (cancel_epi (eqToHom (h M))).1
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      exact (Category.assoc _ _ _).trans hm.symm)
  obtain ⟨j, hj⟩ := scalarIdentity X A'
  let q : G ≅ F := k ≪≫ Functor.isoWhiskerLeft F j ≪≫ Functor.rightUnitor F
  have hq (M : pbcModules Y A) (W : X.ProEtᵒᵖ) (m : (F.obj M).val.obj W) :
      (q.hom.app M).val.app W
        ((eqToHom (h M)).val.app W
          (pbcTensorSection (𝟙 A') (F.obj M) W 1 m)) = m := by
    change (j.hom.app (F.obj M)).val.app W
      ((eqToHom (h M).symm).val.app W
        ((eqToHom (h M)).val.app W
          (pbcTensorSection (𝟙 A') (F.obj M) W 1 m))) = m
    have hh : eqToHom (h M) ≫ eqToHom (h M).symm = 𝟙 _ := by
      simp
    have hv := congrArg (fun f ↦ f.val.app W
      (pbcTensorSection (𝟙 A') (F.obj M) W 1 m)) hh
    change (eqToHom (h M).symm).val.app W
      ((eqToHom (h M)).val.app W
        (pbcTensorSection (𝟙 A') (F.obj M) W 1 m)) = _ at hv
    rw [hv]
    exact hj (F.obj M) W m
  refine ⟨Functor.isoWhiskerRight q (pbcExtend c), ?_⟩
  intro M W s m
  change ((pbcExtend c).map (q.hom.app M)).val.app W _ = _
  rw [section_smul]
  rw [show ((pbcExtend c).map (q.hom.app M)).val.app W (s • _) =
      s • ((pbcExtend c).map (q.hom.app M)).val.app W _ from
    (((pbcExtend c).map (q.hom.app M)).val.app W).hom.map_smul s _]
  rw [← section_naturality]
  erw [hq]
  rw [← section_smul]

end WeilConjectures.AdicQbarRealization.Proper
