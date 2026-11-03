/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativeCoefficientCohomology.CoefficientRootScalarBasis
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralLocalModels
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # The completed basis of a globally framed Tate line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology
open FrobeniusCoefficientTwists

private theorem frame_transition
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) (n : ℕ) :
    (ProEtale.constantTateResidueSystem S l).map
        (homOfLE (Nat.le_succ (n + 1))).op ≫ (A.basis (n + 1)).hom =
      (A.basis (n + 2)).hom ≫
        (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ n)).op := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (proEtaleRootsOfUnitySheaf S (l ^ (n + 1))).property
  ext U x
  obtain ⟨x⟩ := x
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective x
  have hred : ((ProEtale.constantTateResidueSystem S l).map
        (homOfLE (Nat.le_succ (n + 1))).op).hom.app U
      (coefficientRootSection S (l ^ (n + 2)) U a) =
    coefficientRootSection S (l ^ (n + 1)) U a := by
    have h := congrArg (fun f ↦ f.app U (ULift.up (a : ZMod (l ^ (n + 2)))))
      (toSheafify_naturality (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).map (ProEtale.integralResidueAbTransition l (n + 1))))
    have hcast : (ProEtale.integralResidueAbTransition l (n + 1))
        (ULift.up (a : ZMod (l ^ (n + 2)))) = ULift.up (a : ZMod (l ^ (n + 1))) := by
      change ULift.up ((ZMod.castHom (pow_dvd_pow l (Nat.le_add_right (n + 1) 1))
        (ZMod (l ^ (n + 1)))) (a : ZMod (l ^ (n + 2)))) = _
      rw [map_natCast]
    simp only [NatTrans.comp_app, AddCommGrpCat.comp_apply, Functor.const_map_app] at h
    erw [hcast] at h
    have hm : (ProEtale.constantTateResidueSystem S l).map
        (homOfLE (Nat.le_succ (n + 1))).op =
        (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).map
          (ProEtale.integralResidueAbTransition l (n + 1)) := by
      simp only [ProEtale.constantTateResidueSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
    rw [hm]
    exact h.symm
  change (A.basis (n + 1)).hom.hom.app U
      ((((ProEtale.constantTateResidueSystem S l).map
        (homOfLE (Nat.le_succ (n + 1))).op).hom.app U)
        (coefficientRootSection S (l ^ (n + 2)) U a)) =
    ((proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)).map
      (homOfLE (Nat.le_succ n)).op).hom.app U
      ((A.basis (n + 2)).hom.hom.app U
        (coefficientRootSection S (l ^ (n + 2)) U a))
  erw [hred]
  apply (proEtaleRootsOfUnitySections S (l ^ (n + 1)) U).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  have hp := proEtaleRootsOfUnityTransition_prime S l (Fact.out : l.Prime) n U
    ((A.basis (n + 2)).hom.hom.app U
      (coefficientRootSection S (l ^ (n + 2)) U a))
  have hlow :=
    (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 1)) U).exists.choose_spec
      (((proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)).map
      (homOfLE (Nat.le_succ n)).op).hom.app U
        ((A.basis (n + 2)).hom.hom.app U
          (coefficientRootSection S (l ^ (n + 2)) U a)))
  have hhigh :=
    (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 2)) U).exists.choose_spec
      ((A.basis (n + 2)).hom.hom.app U
      (coefficientRootSection S (l ^ (n + 2)) U a))
  simp only [proEtaleRootsOfUnityTower,
    Functor.ofOpSequence_map_homOfLE_succ] at hlow
  erw [← hlow, ← hhigh] at hp
  have hp' := congrArg (fun t ↦ t.down.toMul.val) hp
  change (Additive.toMul (proEtaleRootsOfUnitySections S (l ^ (n + 1)) U _)).val.val =
    (Additive.toMul (proEtaleRootsOfUnitySections S (l ^ (n + 2)) U _)).val.val ^ l at hp'
  rw [A.value] at hp'
  rw [A.value]
  simp only [proEtaleRootsOfUnityTower,
    Functor.ofOpSequence_map_homOfLE_succ]
  erw [hp']
  have hs := congrArg (fun t : Γ(S, ⊤)ˣ ↦ U.unop.hom.appTop.hom (t : Γ(S, ⊤)))
    (A.step (n + 1))
  simpa only [Units.val_pow_eq_pow_val, map_pow, ← pow_mul, Nat.mul_comm] using
    congrArg (fun t ↦ t ^ a) hs.symm

private def frame_tower_iso
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) :
    successorIndex ⋙ ProEtale.constantTateResidueSystem S l ≅
      proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) := by
  let f : successorIndex ⋙ ProEtale.constantTateResidueSystem S l ⟶
      proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) :=
    NatTrans.ofOpSequence (fun n ↦ (A.basis (n + 1)).hom) (by
      intro n
      simpa only [Functor.comp_map, successorIndex_step] using frame_transition S l q g A n)
  exact NatIso.ofComponents (fun n ↦ A.basis (n.unop + 1)) (fun h ↦ f.naturality h)

private def fromOverTerminal
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (T : S.ProEt) (hT : IsTerminal T) {M N : SheafOfModules.{u + 1} R}
    (f : M.over T ⟶ N.over T) : M ⟶ N where
  val :=
    { app U := f.val.app (op (Over.mk (hT.from U.unop)))
      naturality {U V} h := by
        exact f.val.naturality
          (Over.homMk (U := Over.mk (hT.from V.unop))
            (V := Over.mk (hT.from U.unop)) h.unop (hT.hom_ext _ _)).op }

private def fromOverTerminalIso
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) RingCat.{u + 1})
    (T : S.ProEt) (hT : IsTerminal T) {M N : SheafOfModules.{u + 1} R}
    (e : M.over T ≅ N.over T) : M ≅ N where
  hom := fromOverTerminal S R T hT e.hom
  inv := fromOverTerminal S R T hT e.inv
  hom_inv_id := by
    ext U x
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app (op (Over.mk (hT.from U.unop)))) e.hom_inv_id) x
    change e.inv.val.app (op (Over.mk (hT.from U.unop)))
      (e.hom.val.app (op (Over.mk (hT.from U.unop))) x) = x at h
    exact h
  inv_hom_id := by
    ext U x
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app (op (Over.mk (hT.from U.unop)))) e.inv_hom_id) x
    change e.hom.val.app (op (Over.mk (hT.from U.unop)))
      (e.inv.val.app (op (Over.mk (hT.from U.unop))) x) = x at h
    exact h

private def framedIntegerBasis
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) :
    purTwistZlModule S l ≅
      SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l)) := by
  let T : S.ProEt := ProEt.mk (𝟙 S)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ S
  let t := (frame_tower_iso S l q g A).symm ≪≫ (coefficientTowerIso S l).symm
  let tT := Functor.isoWhiskerRight t ((ProEt.topology S).overPullback AddCommGrpCat T)
  exact fromOverTerminalIso S _ T hT (completedBasis S l T tT)

private theorem coefficientTowerIso_one
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) (U : S.ProEtᵒᵖ) :
    ((coefficientTowerIso S l).hom.app (op n)).hom.app U
      (1 : (purTwistFiniteRing S l n).obj.obj U) =
        coefficientRootSection S (l ^ (n + 1)) U 1 := by
  let := forgetCommAbPreserves S
  let F := (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}
  let R := CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  have hf : Functor.whiskerRight
        (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj R)) F ≫
      ((constantCommuteCompose (ProEt.topology S) F).hom.app R).hom =
        toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj (F.obj R)) := by
    rw [constantCommuteCompose_hom_app_hom, ← Category.assoc, sheafComposeIso_inv_fac]
    rw [← toSheafify_naturality]
    ext V x
    rfl
  have hv := congrArg (fun f ↦ f.app U (ULift.up (1 : ZMod (l ^ (n + 1)))) ) hf
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, AddCommGrpCat.comp_apply] at hv
  have ho : (F.map ((toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj R)).app U))
        (ULift.up (1 : ZMod (l ^ (n + 1)))) =
          (1 : (purTwistFiniteRing S l n).obj.obj U) :=
    map_one ((toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj R)).app U).hom
  erw [ho] at hv
  dsimp only [coefficientTowerIso, asIso_hom, NatTrans.ofOpSequence_app,
    coefficientRootSection, F, R, successorIndex,
    ProEtale.constantTateResidueSystem, Functor.comp_obj,
    Functor.ofOpSequence, Functor.leftOp, Functor.ofSequence,
    Functor.const_obj_obj, Iso.app_hom, Functor.op_obj, Opposite.unop_op,
    CommRingCat.hasForgetToRingCat, RingCat.hasForgetToAddCommGrp,
    forget₂, HasForget₂.forget₂, CommRingCat.of, RingCat.of] at *
  convert hv using 1 <;> first | rfl | (simp only [Nat.cast_one]; rfl)

private theorem framedIntegerBasis_root_coordinates
    (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) (U : S.ProEtᵒᵖ) (n : ℕ) :
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
        ((framedIntegerBasis S l q g A).inv.val.app U
          (1 : (purTwistZlCompletion S l).obj.obj U)) =
      (A.basis (n + 1)).hom.hom.app U
        (coefficientRootSection S (l ^ (n + 1)) U 1) := by
  let T : S.ProEt := ProEt.mk (𝟙 S)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ S
  let t := (frame_tower_iso S l q g A).symm ≪≫ (coefficientTowerIso S l).symm
  let tT := Functor.isoWhiskerRight t ((ProEt.topology S).overPullback AddCommGrpCat T)
  let W : (Over T)ᵒᵖ := op (Over.mk (hT.from U.unop))
  let c := framedIntegerBasis S l q g A
  have hc : c.hom.val.app U (c.inv.val.app U (1 : (purTwistZlCompletion S l).obj.obj U)) =
      (1 : (purTwistZlCompletion S l).obj.obj U) :=
    congrArg (fun f ↦ f.val.app U
      (1 : (purTwistZlCompletion S l).obj.obj U)) c.inv_hom_id
  have hp := completedBasis_projection S l T tT n W
    (c.inv.val.app U (1 : (purTwistZlCompletion S l).obj.obj U))
  dsimp only [finiteIsoOfAbIso, moduleIsoOfAddIso,
    PresheafOfModules.restrictHomEquivOfIsLocallySurjective, Equiv.symm,
    PresheafOfModules.homMk, Equiv.coe_fn_mk, PresheafOfModules.toPresheaf,
    tT, t, W, framedIntegerBasis, fromOverTerminalIso, fromOverTerminal,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.comp_app] at hp
  change (purTwistZlProjection S l n).hom.app U
      (c.hom.val.app U (c.inv.val.app U (1 : (purTwistZlCompletion S l).obj.obj U))) =
    ((coefficientTowerIso S l).inv.app (op n)).hom.app U
      ((A.basis (n + 1)).inv.hom.app U
        ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
          (c.inv.val.app U (1 : (purTwistZlCompletion S l).obj.obj U)))) at hp
  rw [hc, map_one] at hp
  have hp' := congrArg (((coefficientTowerIso S l).hom.app (op n)).hom.app U) hp
  have hid (x : (coefficientRootConstants S (l ^ (n + 1))).obj.obj U) :
      ((coefficientTowerIso S l).hom.app (op n)).hom.app U
        (((coefficientTowerIso S l).inv.app (op n)).hom.app U x) = x := by
    exact congrArg (fun f ↦ f.hom.app U x)
      ((coefficientTowerIso S l).app (op n)).inv_hom_id
  rw [coefficientTowerIso_one, hid] at hp'
  have hb := congrArg ((A.basis (n + 1)).hom.hom.app U) hp'
  have hi (x : (proEtaleRootsOfUnitySheaf S (l ^ (n + 1))).obj.obj U) :
      (A.basis (n + 1)).hom.hom.app U ((A.basis (n + 1)).inv.hom.app U x) = x :=
    congrArg (fun f ↦ f.hom.app U x) (A.basis (n + 1)).inv_hom_id
  exact (hb.trans (hi _)).symm

private def framedIntegralBasis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) :
    positiveLine l E S 0 ≅ positiveLine l E S 1 := by
  let φ := purTwistCompletedScalarMap S l E
  let c := framedIntegerBasis S l q g A
  have := integralExtensionReverse_isIso S l E
  exact (SheafOfModules.scalarExtensionUnitIso φ).symm ≪≫
    (PurScalar.tensorFunctor φ).mapIso c.symm ≪≫ asIso (integralExtensionReverse S l E)

set_option maxHeartbeats 1500000 in
-- The section formulas compare several coefficient-ring presentations.
private theorem framedIntegralBasis_value
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) (U : S.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U) :
    (framedIntegralBasis l E S q g A).hom.val.app U a =
      @SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul a
        (purTwistIntegralTensor S l E U 1
        ((framedIntegerBasis S l q g A).inv.val.app U
          (1 : (purTwistZlCompletion S l).obj.obj U))) := by
  let φ := purTwistCompletedScalarMap S l E
  let c := framedIntegerBasis S l q g A
  have hu : (SheafOfModules.scalarExtensionUnitIso φ).inv.val.app U a =
      SheafOfModules.scalarExtensionSection φ (SheafOfModules.unit _) U a
        (1 : (purTwistZlCompletion S l).obj.obj U) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation _ U).map
        (SheafOfModules.scalarExtensionUnitIso φ).hom)).1
    have h := congrArg (fun f ↦ f.val.app U a)
      (SheafOfModules.scalarExtensionUnitIso φ).inv_hom_id
    change (SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U
      ((SheafOfModules.scalarExtensionUnitIso φ).inv.val.app U a) = a at h
    change (SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U _ =
      (SheafOfModules.scalarExtensionUnitIso φ).hom.val.app U _
    rw [h]
    have ht := SheafOfModules.scalarExtensionUnitIso_tmul φ U a
      (1 : (purTwistZlCompletion S l).obj.obj U)
    simpa only [map_one, mul_one] using ht.symm
  change (integralExtensionReverse S l E).val.app U
    (((PurScalar.tensorFunctor φ).map c.inv).val.app U
      ((SheafOfModules.scalarExtensionUnitIso φ).inv.val.app U a)) = _
  rw [hu]
  have hm := SheafOfModules.scalarExtension_map_tmul φ c.inv U a
    (1 : (purTwistZlCompletion S l).obj.obj U)
  change ((PurScalar.tensorFunctor φ).map c.inv).val.app U _ = _ at hm
  rw [hm]
  exact integralExtensionReverse_section S l E U a _

set_option maxHeartbeats 1000000 in
-- Tensor identities traverse the site tensor sheafification.
private def secondFactorIso
    (S : Scheme.{u}) (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1} (purTwistRing S R))
    {N N' : SheafOfModules.{u + 1} (purTwistRing S R)} (e : N ≅ N') :
    (SheafOfModules.siteSheafTensorRight N).obj M ≅
      (SheafOfModules.siteSheafTensorRight N').obj M where
  hom := SheafOfModules.siteSheafTensorSecondMap M e.hom
  inv := SheafOfModules.siteSheafTensorSecondMap M e.inv
  hom_inv_id := by
    apply SheafOfModules.scalarTensor_hom_ext
    intro U x y
    change (SheafOfModules.siteSheafTensorSecondMap M e.inv).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap M e.hom).val.app U
        (SheafOfModules.siteSheafTensorTmul M N U x y)) = _
    rw [SheafOfModules.scalarTensor_second_tmul M e.hom U x y,
      SheafOfModules.scalarTensor_second_tmul M e.inv U x _]
    exact congrArg (SheafOfModules.siteSheafTensorTmul M N U x)
      (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) e.hom_inv_id) y)
  inv_hom_id := by
    apply SheafOfModules.scalarTensor_hom_ext
    intro U x y
    change (SheafOfModules.siteSheafTensorSecondMap M e.hom).val.app U
      ((SheafOfModules.siteSheafTensorSecondMap M e.inv).val.app U
        (SheafOfModules.siteSheafTensorTmul M N' U x y)) = _
    rw [SheafOfModules.scalarTensor_second_tmul M e.inv U x y,
      SheafOfModules.scalarTensor_second_tmul M e.hom U x _]
    exact congrArg (SheafOfModules.siteSheafTensorTmul M N' U x)
      (ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) e.inv_hom_id) y)

private def framedPositiveBasis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) :
    ∀ d : ℕ, positiveLine l E S 0 ≅ positiveLine l E S d
  | 0 => Iso.refl _
  | 1 => framedIntegralBasis l E S q g A
  | d + 2 =>
    (SheafOfModules.scalarTensorRightUnitor
      (completedIntegralCommRingSheafUnrestricted l E S) (positiveLine l E S 0)).symm ≪≫
    (SheafOfModules.siteSheafTensorRight (positiveLine l E S 0)).mapIso
      (framedPositiveBasis l E S q g A (d + 1)) ≪≫
    secondFactorIso S (completedIntegralCommRingSheafUnrestricted l E S)
      (positiveLine l E S (d + 1)) (framedIntegralBasis l E S q g A)

set_option maxHeartbeats 1500000 in
-- The section formulas compare several coefficient-ring presentations.
private theorem framedPositiveBasis_value
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) : ∀ (d : ℕ) (U : S.ProEtᵒᵖ)
    (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U),
    (framedPositiveBasis l E S q g A d).hom.val.app U a =
      generator l E S U a d
        (fun _ ↦ (framedIntegerBasis S l q g A).inv.val.app U
          (1 : (purTwistZlCompletion S l).obj.obj U)) := by
  apply Nat.twoStepInduction
  · intros; rfl
  · intro U a
    exact framedIntegralBasis_value l E S q g A U a
  · intro d _ ih U a
    let R := completedIntegralCommRingSheafUnrestricted l E S
    let M := positiveLine l E S 0
    have hu : (SheafOfModules.scalarTensorRightUnitor R M).inv.val.app U a =
        SheafOfModules.siteSheafTensorTmul M M U a
          (1 : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U) := by
      apply (ConcreteCategory.bijective_of_isIso
        ((SheafOfModules.evaluation _ U).map
          (SheafOfModules.scalarTensorRightUnitor R M).hom)).1
      have h := congrArg (fun f ↦ f.val.app U a)
        (SheafOfModules.scalarTensorRightUnitor R M).inv_hom_id
      change (SheafOfModules.scalarTensorRightUnitor R M).hom.val.app U _ =
        (SheafOfModules.scalarTensorRightUnitor R M).hom.val.app U _
      change (SheafOfModules.scalarTensorRightUnitor R M).hom.val.app U
        ((SheafOfModules.scalarTensorRightUnitor R M).inv.val.app U a) = a at h
      rw [h]
      have ht := SheafOfModules.scalarTensorRightUnitor_tmul R M U a
        (1 : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)
      change a = (SheafOfModules.scalarTensorRightUnitor R M).hom.val.app U
        (SheafOfModules.siteSheafTensorTmul M (SheafOfModules.unit _) U a
          (1 : R.obj.obj U))
      simpa only [one_smul] using ht.symm
    dsimp only [framedPositiveBasis, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      secondFactorIso]
    change (SheafOfModules.siteSheafTensorSecondMap (positiveLine l E S (d + 1))
      (framedIntegralBasis l E S q g A).hom).val.app U
        (((SheafOfModules.siteSheafTensorRight M).map
          (framedPositiveBasis l E S q g A (d + 1)).hom).val.app U
            ((SheafOfModules.scalarTensorRightUnitor R M).inv.val.app U a)) = _
    rw [hu]
    erw [SheafOfModules.scalarTensor_first_tmul
      (framedPositiveBasis l E S q g A (d + 1)).hom M U a
        (1 : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)]
    erw [SheafOfModules.scalarTensor_second_tmul (positiveLine l E S (d + 1))
      (framedIntegralBasis l E S q g A).hom U _
        (1 : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U)]
    rw [ih, framedIntegralBasis_value]
    have hone (x : (purTwistIntegralModule S l E).val.obj U) :
        @SMul.smul _ _ (purTwistIntegralAction S l E U).toSMul
          (1 : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U) x = x :=
      by
        let := purTwistIntegralAction S l E U
        exact one_smul _ x
    erw [hone]
    rfl

/-- Compatible finite primitive-root frames give a global completed coefficient
basis in every positive tensor power, normalized by the root with coordinates one.

Source: coefficient-twist blueprint, inverse limit, integral scalar extension and ordered powers.
(blueprint: lem-sf-coefficient-tate-completed-basis).

Proof: the root value formula and the prime-power transition identify the finite
basis transition squares. This gives an isomorphism of the finite constant-residue
and root diagrams. Apply the inverse-limit comparison and coordinatewise linearity
of the completed root action. Evaluate the inverse basis on one to obtain compatible
root sections with all finite frame coordinates one. Extend this completed basis
along the completed coefficient map. The normalized scalar-extension isomorphism
identifies the resulting module with the integral root line and sends a tensor
a tensor z to a times the prescribed integral root generator. Tensor these bases
in the prescribed left-associated order. The inverse regular-module multiplication
inserts a tensor one, so induction gives exactly the stated ordered generator
formula. The zero power is the identity, and the empty scheme uses the same limits. -/
theorem coefficient_tate_completed_basis
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (q : ℕ) (g : S ⟶ S)
    (A : CoefficientTateRootFrames S l q g) (d : ℕ) :
    ∃ z : ∀ U : S.ProEtᵒᵖ, (purTwistZlOne S l).obj.obj U,
      (∀ U n,
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
            (z U) =
          (A.basis (n + 1)).hom.hom.app U
            (coefficientRootSection S (l ^ (n + 1)) U 1)) ∧
      ∃ b : positiveLine l E S 0 ≅ positiveLine l E S d,
        ∀ U (a : (completedIntegralCoefficientSheafUnrestricted l E S).obj.obj U),
          b.hom.val.app U a = generator l E S U a d (fun _ ↦ z U) := by
  refine ⟨fun U ↦ (framedIntegerBasis S l q g A).inv.val.app U
          (1 : (purTwistZlCompletion S l).obj.obj U),
    framedIntegerBasis_root_coordinates S l q g A,
    framedPositiveBasis l E S q g A d, ?_⟩
  exact framedPositiveBasis_value l E S q g A d

end WeilConjectures.NativeCoefficientCohomology
