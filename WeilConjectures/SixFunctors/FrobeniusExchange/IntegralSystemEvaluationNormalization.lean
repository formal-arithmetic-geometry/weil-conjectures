/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Right.RightDerivedMateIndependence
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Normalized right-derived evaluation of strict integral systems

(blueprint: lem-weil-integral-system-evaluation-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FrobeniusExchange
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private abbrev rs (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private abbrev qs (n : ℕ) : rs l E (n + 1) ⟶ rs l E n :=
  CommRingCat.ofHom (Padic.coefficientExtensionTransition l E (n + 1)).ulift
attribute [local implicit_reducible] coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition integralCoefficientCommRingSheaf
  integralCoefficientSheafTransition ProEtale.VaryingRing.coefficientTransition
  SemilinearSections.systemRing SemilinearSections.ringPresheaf SemilinearSections.rings
  integralComparisonSequencePullback integralCoefficientSheaf
attribute [local irreducible] constantSheaf Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local instance] ProEtale.VaryingRing.pullAdditive
private theorem finitePush_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n+1)) =
      ProEtale.StrictTower.moduleDirectImage (rs l E n) f := by
  unfold proEtaleConstantModuleDirectImage ProEtale.StrictTower.moduleDirectImage
  congr 1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hb := ((proEtaleSheafAdjunction f CommRingCat.{u+1}).homEquiv _ _).apply_symm_apply
    (proEtaleConstantDirectImageMap f CommRingCat.{u+1} (rs l E n))
  exact (congrArg (fun t ↦ (forget₂ CommRingCat.{u+1} RingCat.{u+1}).map
    (t.hom.app U)) hb).symm
section Invariance
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  {L Q : B ⥤ A} {R : A ⥤ B} {L' Q' : D ⥤ C} {R' : C ⥤ D}
  (G : B ⥤ D) (H : A ⥤ C)
  [L.Additive] [qAdditive : Q.Additive] [R.Additive]
  [L'.Additive] [Q'.Additive] [R'.Additive] [gAdditive : G.Additive] [hAdditive : H.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [qLimits : PreservesFiniteLimits Q] [qColimits : PreservesFiniteColimits Q]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits Q'] [PreservesFiniteColimits Q']
  [gLimits : PreservesFiniteLimits G] [gColimits : PreservesFiniteColimits G]
  [hLimits : PreservesFiniteLimits H] [hColimits : PreservesFiniteColimits H]
private theorem derivedMate_isIso_of_rightEqualities
    {T : A ⥤ B} [tAdditive : T.Additive] {S : C ⥤ D} [S.Additive]
    {G' : B ⥤ D} {H' : A ⥤ C} [gnAdditive : G'.Additive] [hnAdditive : H'.Additive]
    [gnLimits : PreservesFiniteLimits G'] [gnColimits : PreservesFiniteColimits G']
    [hnLimits : PreservesFiniteLimits H'] [hnColimits : PreservesFiniteColimits H']
    (a : L ⊣ R) (b : L' ⊣ R') (c : Q ⊣ T) (d : Q' ⊣ S)
    (θ : G ⋙ L' ≅ L ⋙ H) (ψ : G' ⋙ Q' ≅ Q ⋙ H')
    (hT : R = T) (hR : R' = S) (hG : G = G') (hH : H = H')
    (ha : IsIso (mateEquiv a b θ.hom).natTrans)
    (hb : IsIso (mateEquiv c d ψ.hom).natTrans)
    (hi : IsIso (mateEquiv c.mapDerivedCategoryRightDerivedAdjunction
      d.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso ψ).hom).natTrans) :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso θ).hom).natTrans := by
  subst T
  subst S
  subst G'
  subst H'
  exact rightDerivedMate_isIso_of_ordinaryMate_isIso G H a b c d θ ψ ha hb hi
end Invariance
private theorem varyingModuleEvalMate (R : ℕ → CommRingCat.{u + 1})
    (q : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (ProEtale.VaryingRing.moduleAdj R q f)
      (proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
        (ProEtale.VaryingRing.coefficients R X n)
        (ProEtale.StrictTower.constantRingIso (R n) f))
      (ProEtale.VaryingRing.moduleEvalG R q f n).inv).natTrans =
        (ProEtale.VaryingRing.moduleEvalP R q f n).hom := by
  let a := ProEtale.VaryingRing.moduleAdj R q f
  let b := proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
    (ProEtale.VaryingRing.coefficients R X n)
    (ProEtale.StrictTower.constantRingIso (R n) f)
  have hh := ProEtale.VaryingRing.inverseMateEqOfUnit a b
    (ProEtale.VaryingRing.eval R q Y n) (ProEtale.VaryingRing.eval R q X n)
    (ProEtale.VaryingRing.moduleEvalP R q f n).hom
    (ProEtale.VaryingRing.moduleEvalG R q f n)
    (ProEtale.VaryingRing.moduleEvalG_existsUnique R q f n).choose_spec.1
  have he : (mateEquiv a b).symm
      (TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalP R q f n).hom) =
      TwoSquare.mk _ _ _ _ (ProEtale.VaryingRing.moduleEvalG R q f n).inv := by
    apply TwoSquare.ext
    intro M
    exact congr_app hh M
  have he' := congrArg (mateEquiv a b) he
  rw [Equiv.apply_symm_apply] at he'
  exact (congrArg TwoSquare.natTrans he').symm

private theorem varyingDerivedMateIso (R : ℕ → CommRingCat.{u + 1})
    (q : ∀ n, R (n + 1) ⟶ R n) {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (mateEquiv
      (ProEtale.VaryingRing.moduleAdj R q f).mapDerivedCategoryRightDerivedAdjunction
      (proEtaleRingModuleAdjunction f (ProEtale.VaryingRing.coefficients R Y n)
        (ProEtale.VaryingRing.coefficients R X n)
        (ProEtale.StrictTower.constantRingIso (R n) f)).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.VaryingRing.moduleEvalG R q f n).symm).hom).natTrans := by
  rw [ProEtale.VaryingRing.square_symm]
  exact ProEtale.VaryingRing.evalPMate_isIso R q f n

set_option maxHeartbeats 1000000 in
-- Comparing the derived functors in the two coefficient coordinates needs extra elaboration steps.
/-- An ordinary invertible evaluation mate for strict integral systems has an
invertible canonical right-derived mate for the actual integral pullback models.
Source: Zheng 4.10; Stacks Tags 070I, 070K and 07A7
(blueprint: lem-weil-integral-system-evaluation-normalization).

Identify the finite direct-image functor with the varying-ring direct image by the
ring-sheaf adjunction inverse equation. The varying-ring ordinary and derived
comparison mates are invertible. The general cochain-normalization argument then
transfers derived invertibility to the given ordinary invertible mate. -/
theorem integralSystemEvaluationMate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [(integralComparisonSequenceDirectImage l E f).Additive]
    [Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X)]
    (a : integralComparisonSequencePullback l E f ⊣
      integralComparisonSequenceDirectImage l E f)
    (b : sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⊣
      proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)))
    (θ : coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n)
    (hθ : IsIso (mateEquiv a b θ.hom).natTrans) :
    letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteLimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := sfIntrinsicPullback_preservesFiniteColimits
      (Padic.coefficientExtensionRing l E (n + 1)) f
    letI := coefficientSequenceEvaluation_additiveInstance l E X n
    letI := coefficientSequenceEvaluation_additiveInstance l E Y n
    letI := coefficientSequenceEvaluation_limits l E X n
    letI := coefficientSequenceEvaluation_limits l E Y n
    letI := coefficientSequenceEvaluation_colimits l E X n
    letI := coefficientSequenceEvaluation_colimits l E Y n
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      ((Functor.mapDerivedCategoryCompIso
        (coefficientSequenceEvaluation l E Y n)
        (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f) ≪≫
        Functor.mapDerivedCategoryNatIso θ ≪≫
        (Functor.mapDerivedCategoryCompIso
          (integralComparisonSequencePullback l E f)
          (coefficientSequenceEvaluation l E X n)).symm).hom)).natTrans := by
  let : Abelian.HasKInjectiveResolutions (normalizedDVRModules l E X n) :=
    proEtaleRingModules_hasKInjectiveResolutions X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n + 1)))
  let qadd : (ProEtale.VaryingRing.pull (rs l E) (qs l E) f).Additive :=
    (ProEtale.VaryingRing.pull_exact (rs l E) (qs l E) f).1
  have : PreservesFiniteLimits (ProEtale.VaryingRing.pull (rs l E) (qs l E) f) :=
    (ProEtale.VaryingRing.pull_exact (rs l E) (qs l E) f).2.1
  have : PreservesFiniteColimits (ProEtale.VaryingRing.pull (rs l E) (qs l E) f) :=
    (ProEtale.VaryingRing.pull_exact (rs l E) (qs l E) f).2.2
  let G := coefficientSequenceEvaluation l E Y n
  let H := coefficientSequenceEvaluation l E X n
  have h₂ : (mateEquiv (ProEtale.VaryingRing.moduleAdj (rs l E) (qs l E) f)
    (proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (rs l E) Y n)
    (ProEtale.VaryingRing.coefficients (rs l E) X n)
    (ProEtale.StrictTower.constantRingIso (rs l E n) f))
      (ProEtale.VaryingRing.moduleEvalG (rs l E) (qs l E) f n).inv).natTrans =
      (ProEtale.VaryingRing.moduleEvalP (rs l E) (qs l E) f n).hom := by
    exact varyingModuleEvalMate (rs l E) (qs l E) f n
  have hb : IsIso (mateEquiv
    (ProEtale.VaryingRing.moduleAdj (rs l E) (qs l E) f) (proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (rs l E) Y n)
    (ProEtale.VaryingRing.coefficients (rs l E) X n)
    (ProEtale.StrictTower.constantRingIso (rs l E n) f))
      (ProEtale.VaryingRing.moduleEvalG (rs l E) (qs l E) f n).inv).natTrans := by
    rw [h₂]
    exact ProEtale.VaryingRing.moduleEvalP_hom_isIso (rs l E) (qs l E) f n
  have hi := varyingDerivedMateIso (rs l E) (qs l E) f n
  apply derivedMate_isIso_of_rightEqualities
    (G := G) (H := H)
    (Q := ProEtale.VaryingRing.pull (rs l E) (qs l E) f)
    (qAdditive := qadd)
    (tAdditive := ProEtale.VaryingRing.push_additive (rs l E) (qs l E) f)
    (gnAdditive := coefficientSequenceEvaluation_additiveInstance l E Y n)
    (hnAdditive := coefficientSequenceEvaluation_additiveInstance l E X n)
    (gnLimits := coefficientSequenceEvaluation_limits l E Y n)
    (gnColimits := coefficientSequenceEvaluation_colimits l E Y n)
    (hnLimits := coefficientSequenceEvaluation_limits l E X n)
    (hnColimits := coefficientSequenceEvaluation_colimits l E X n)
    (qLimits := (ProEtale.VaryingRing.pull_exact (rs l E) (qs l E) f).2.1)
    (qColimits := (ProEtale.VaryingRing.pull_exact (rs l E) (qs l E) f).2.2)
    (gAdditive := coefficientSequenceEvaluation_additiveInstance l E Y n)
    (hAdditive := coefficientSequenceEvaluation_additiveInstance l E X n)
    (gLimits := coefficientSequenceEvaluation_limits l E Y n)
    (gColimits := coefficientSequenceEvaluation_colimits l E Y n)
    (hLimits := coefficientSequenceEvaluation_limits l E X n)
    (hColimits := coefficientSequenceEvaluation_colimits l E X n)
    (L := integralComparisonSequencePullback l E f)
    (R := integralComparisonSequenceDirectImage l E f)
    (T := ProEtale.VaryingRing.push (rs l E) (qs l E) f)
    (L' := sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f)
    (R' := proEtaleConstantModuleDirectImage f
      (Padic.coefficientExtensionRing l E (n + 1))) a b
    (ProEtale.VaryingRing.moduleAdj (rs l E) (qs l E) f) (proEtaleRingModuleAdjunction f
    (ProEtale.VaryingRing.coefficients (rs l E) Y n)
    (ProEtale.VaryingRing.coefficients (rs l E) X n)
    (ProEtale.StrictTower.constantRingIso (rs l E n) f)) θ
    (ProEtale.VaryingRing.moduleEvalG (rs l E) (qs l E) f n).symm
    (by rfl) (finitePush_eq l E f n) (by rfl) (by rfl) hθ hb
    ?_
  clear h₂ hb
  exact hi
end WeilConjectures.FrobeniusExchange
