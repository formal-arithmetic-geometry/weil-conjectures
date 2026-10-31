/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportGeometry
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompletedCoefficientChange
import WeilConjectures.SixFunctors.IntegralOrdinary.IntegralOrdinaryPullbackComparison

/-! # Balanced finite integral scalar extension and native inverse image

Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15; Stacks Tags 03D2 and 03EK.
(blueprint: lem-sf-native-pullback-integral-module-balance)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicQbarRealization.Proper
open LocallyFiniteAdicCompactSupport
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  (O : Operations l p R S)

/-- The normalized native coefficient map commutes with the normalized finite integral
inclusions. Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-module-balance).

Proof: construct the native geometric coefficient system. Its pullback map and O's
coefficient map have the same adjunct on every locally finite function, hence are equal.
The completed-to-native coefficient change has a commuting pullback square, and its
integral maps agree with any normalized coefficient presentation. Apply this to R and S.
The assertion uses all test objects, including the empty object. -/
private theorem nativePullbackIntegralCoefficientSquare (E : Index l (PadicAlgCl l)) :
    ((PurCompactSupport.completed l (Coefficient.{u} l (PadicAlgCl l) E)).pull p).hom ≫
        coefficientMap l X R E =
      (adicTowerInverseImage p).map (coefficientMap l Y S E) ≫ O.coefficient := by
  let : NativeGeometry.{u} l := Classical.choice (native_compact_support_geometry l)
  have hc : (NativeRings.pull (l := l) p).hom = O.coefficient := by
    apply ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _).injective
    apply Sheaf.hom_ext
    ext V s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact (NativeRings.pull_normalized p V s x).trans (O.functions V s x).symm
  obtain ⟨a, ha⟩ := native_completed_coefficient_change l
    (Coefficient.{u} l (PadicAlgCl l) E) (LocallyFiniteAdicRealization.embedding l E)
  have hX : a.map X = coefficientMap l X R E := ha X (R.coefficient E)
  have hY : a.map Y = coefficientMap l Y S E := ha Y (S.coefficient E)
  have h := a.square p
  rw [hX, hY] at h
  exact h.trans (congrArg ((adicTowerInverseImage p).map (coefficientMap l Y S E) ≫ ·) hc)

set_option maxHeartbeats 800000 in
-- The coefficient and adjunction unit transports require additional elaboration steps.
/-- Balanced tensor extension commutes with ordinary native pullback, fixing the two
insertion-of-one units. Source: Bhatt--Scholze, Remark 6.8.15; Stacks Tags 03D2 and 03EK.
(blueprint: lem-sf-native-pullback-integral-module-balance).

Proof: take adjuncts of the coefficient square. Restriction of scalars commutes with
module direct image by the identity on underlying sections; its linearity is exactly
that square. The ordinary integral pullback followed by native scalar extension and
the reversed composite are therefore left adjoints to naturally isomorphic right
adjoints. Uniqueness of left adjoints gives balance. Its adjunction-unit identity,
evaluated on a section, is precisely the displayed tensor-unit formula. This argument
requires no flatness or nonempty-scheme hypothesis. -/
theorem nativePullbackIntegralModuleBalance (E : Index l (PadicAlgCl l)) :
    ∃ b : ordinaryIntegralModulePull l (Coefficient.{u} l (PadicAlgCl l) E) p ⋙
          pbcExtend (coefficientMap l X R E) ≅
        pbcExtend (coefficientMap l Y S E) ⋙ ContinuousRational.modulePull p O.coefficient,
      ∀ (M : integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) Y)
        (V : Y.ProEt) (m : M.val.obj (op V)),
      (b.hom.app M).val.app (op ((proEtaleBaseChange p).obj V))
        (pbcTensorSection (coefficientMap l X R E)
          ((ordinaryIntegralModulePull l (Coefficient.{u} l (PadicAlgCl l) E) p).obj M)
          (op ((proEtaleBaseChange p).obj V)) 1
          (((ordinaryIntegralModuleAdjunction l (Coefficient.{u} l (PadicAlgCl l) E)
            p).unit.app M).val.app (op V) m)) =
        ContinuousRational.moduleUnit p O.coefficient
          ((pbcExtend (coefficientMap l Y S E)).obj M) V
          (pbcTensorSection (coefficientMap l Y S E) M (op V) 1 m) := by
  let K := Coefficient.{u} l (PadicAlgCl l) E
  let aX := coefficientMap l X R E
  let aY := coefficientMap l Y S E
  let ρ := (proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _ O.coefficient
  have hd : aY ≫ ρ = sfCompletedCoefficientMap l K p ≫
      (proEtaleSheafDirectImage p CommRingCat.{u + 1}).map aX := by
    have h := congrArg ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _)
      (nativePullbackIntegralCoefficientSquare l p R S O E)
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_left] at h
    change _ = aY ≫ ρ at h
    simpa only [PurCompactSupport.completed, PurCompactSupport.completedPullMap, asIso_hom,
      Equiv.apply_symm_apply] using h.symm
  let r : pbcRestrict aX ⋙ ordinaryIntegralModulePush l K p ≅
      ContinuousRational.DirectImage.modulePush p O.coefficient ⋙ pbcRestrict aY := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
      · let P := ((pbcRestrict aX ⋙ ordinaryIntegralModulePush l K p).obj M).val.obj V
        let Q := ((ContinuousRational.DirectImage.modulePush p O.coefficient ⋙
          pbcRestrict aY).obj M).val.obj V
        have hs (s : (completedIntegralCommRingSheafUnrestricted l K Y).obj.obj V) :
            aX.hom.app ((proEtaleBaseChange p).op.obj V)
              ((sfCompletedCoefficientMap l K p).hom.app V s) =
            ρ.hom.app V (aY.hom.app V s) :=
          (congrArg (fun t ↦ t.hom.app V s) hd).symm
        have ho := IntegralOrdinary.directRing_eq l K p
        refine
          { hom := ModuleCat.ofHom (X := P) (Y := Q)
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := ?_ }
            inv := ModuleCat.ofHom (X := Q) (Y := P)
              { toFun := id
                map_add' := fun _ _ ↦ rfl
                map_smul' := ?_ }
            hom_inv_id := by ext; rfl
            inv_hom_id := by ext; rfl }
        · intro s m
          change aX.hom.app ((proEtaleBaseChange p).op.obj V)
            ((ordinaryIntegralDirectRingMap l K p).hom.app V s) •
              (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m) = _
          change aX.hom.app ((proEtaleBaseChange p).op.obj V)
            ((ordinaryIntegralDirectRingMap l K p).hom.app V s) •
              (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m) =
            ρ.hom.app V (aY.hom.app V s) •
              (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m)
          rw [← ho]
          exact congrArg (fun z ↦ z •
            (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m)) (hs s)
        · intro s m
          change ρ.hom.app V (aY.hom.app V s) •
            (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m) =
              aX.hom.app ((proEtaleBaseChange p).op.obj V)
                ((ordinaryIntegralDirectRingMap l K p).hom.app V s) •
                  (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m)
          rw [← ho]
          exact congrArg (fun z ↦ z •
            (show M.val.obj ((proEtaleBaseChange p).op.obj V) from m)) (hs s).symm
      · intros
        ext m
        rfl
    · intro M N f
      ext V m
      rfl
  let a := (ordinaryIntegralModuleAdjunction l K p).comp (pbcScalarAdjunction aX)
  let d := ((pbcScalarAdjunction aY).comp O.moduleAdjunction).ofNatIsoRight r.symm
  let b := a.leftAdjointUniq d
  refine ⟨b, ?_⟩
  intro M V m
  have h := congrArg (fun t ↦ t.val.app (op V) m)
    (a.unit_leftAdjointUniq_hom_app d M)
  change (b.hom.app M).val.app (op ((proEtaleBaseChange p).obj V))
    (((pbcScalarAdjunction aX).unit.app
      ((ordinaryIntegralModulePull l K p).obj M)).val.app
      (op ((proEtaleBaseChange p).obj V))
      (((ordinaryIntegralModuleAdjunction l K p).unit.app M).val.app (op V) m)) =
    (O.moduleAdjunction.unit.app ((pbcExtend aY).obj M)).val.app (op V)
      (((pbcScalarAdjunction aY).unit.app M).val.app (op V) m) at h
  have hX := (pbcScalarAdjunction_exists aX).exists.choose_spec
    ((ordinaryIntegralModulePull l K p).obj M) (op ((proEtaleBaseChange p).obj V))
    (((ordinaryIntegralModuleAdjunction l K p).unit.app M).val.app (op V) m)
  have hY := (pbcScalarAdjunction_exists aY).exists.choose_spec M (op V) m
  change ((pbcScalarAdjunction aX).unit.app _).val.app _ _ = _ at hX
  change ((pbcScalarAdjunction aY).unit.app M).val.app _ _ = _ at hY
  rw [hX, hY, O.unit_sections] at h
  exact h

end WeilConjectures.AdicQbarRealization.Proper
