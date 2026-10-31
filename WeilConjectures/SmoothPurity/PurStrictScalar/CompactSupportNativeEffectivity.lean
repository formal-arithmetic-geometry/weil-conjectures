/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.CompactSupportScalarLimitFoundations
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Effectivity of the specified native compact-support tower

Source: Stacks Tags 0940 and 0941; normalized DVR effectivity applied to the
actual proper/open coefficient sequence.
(blueprint: lem-pur-compact-support-native-effectivity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.PurStrictScalar

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  HasDerivedCategory.standard

private theorem change_adjunction
    {C B : Type*} [Category C] [Category B] {L L' : C ⥤ B} {R : B ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R) {M : C} {N : B} (p : M ⟶ R.obj N) :
    (a.homEquiv M N).symm p =
      (a.leftAdjointUniq b).hom.app M ≫ (b.homEquiv M N).symm p := by
  apply (a.homEquiv M N).injective
  rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right,
    a.homEquiv_leftAdjointUniq_hom_app]
  rw [← b.homEquiv_unit, Equiv.apply_symm_apply]

/-- The native completed limit is derived complete; its actual projection adjuncts
are coherent and its finite compact-support counits are isomorphisms.
Source: Stacks Tag 0941, normalizedDVRTower_effectivity; Tag 07A6, adjoint uniqueness.
(blueprint: lem-pur-compact-support-native-effectivity).
Proof: form the normalized DVR tower with finite objects the native coefficient
sequence evaluations, transitions its actual derived quotient maps, and underlying
tower its exact completed-scalar restriction. The finite-action theorem supplies
normalization. The canonical completed-tower Roos triangle has exactly the specified
limit projections. Normalized DVR effectivity therefore gives completeness and all
finite projection-adjunct isomorphisms and quotient cocycles. The finite support
presentation composes each native counit with its evaluation isomorphism; uniqueness
of left adjoints identifies the change of reduction convention with finiteReductionIso.
Thus the specified compact-support counit is a composite of three isomorphisms. -/
theorem compactSupport_native_effectivity
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) (hK : sfIntegralConstructible l E X K) :
    IsSfDerivedComplete l E Y ((scalarSupport l E c S).obj K) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      scalarSupportNativeCounit l E c S m K ≫
          (coefficientSequenceDerivedTransition l E Y h).app
            ((scalarSupportNative l E c S).obj K) =
        normalizedDVRReductionTransition l E Y D hl h ((scalarSupport l E c S).obj K) ≫
          (normalizedDVRRes l E Y h).map (scalarSupportNativeCounit l E c S n K)) ∧
    ∀ n : ℕ, IsIso (scalarSupportCounit l E c S n K) := by
  let N := (scalarSupportNative l E c S).obj K
  let T : NormalizedDVRTower l E Y D hl := {
    M := fun n ↦ (coefficientSequenceDerivedEvaluation l E Y n).obj N
    tau := fun h ↦ (coefficientSequenceDerivedTransition l E Y h).app N
    tau_refl := derivedTransition_id l E Y N
    tau_comp := fun h₁ h₂ ↦ derivedTransition_comp l E Y N h₁ h₂
    tower := (coefficientSequenceDerivedRestriction l E Y).obj N
    evaluationIso := fun n ↦ (coefficientRestrictedEvaluationIso l E Y n).app N
    tower_tau := fun h ↦ derivedRestrictedTransition l E Y D hl N h
    normalization := compactSupportSystem_normalized l c D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) E ⟨K, hK⟩ S }
  obtain ⟨hp, δ, hδ⟩ := coefficientConstantTower_roos l E Y D hl T.tower
  have hpDVR : HasProduct (fun n : ℕ ↦
      (normalizedDVRTowerEvaluation l E Y D hl n).obj T.tower) := hp
  let := hpDVR
  let p := Pi.lift (fun n : ℕ ↦ (coefficientConstantTowerProjection l E Y n).app T.tower)
  obtain ⟨hi, hc, hcomplete⟩ := normalizedDVRTower_effectivity l E Y D hl T
    ((scalarSupport l E c S).obj K) p δ hδ
  have heq (n : ℕ) :
      normalizedDVRCounitComparison l E Y D hl T ((scalarSupport l E c S).obj K) p n =
        scalarSupportNativeCounit l E c S n K := by
    unfold normalizedDVRCounitComparison scalarSupportNativeCounit
    change ((coefficientFiniteAdjunction l E Y n).homEquiv _ _).symm _ = _
    congr 1
    dsimp only [p]
    erw [Pi.lift_π_assoc]
    rfl
  have hn (n : ℕ) : IsIso (scalarSupportNativeCounit l E c S n K) := by
    rw [← heq n]
    exact hi n
  refine ⟨(sfDerivedComplete_iff_legacy l E Y D hl _).mpr hcomplete, ?_, ?_⟩
  · intro m n h
    simpa only [heq] using hc h
  · intro n
    have hfac : scalarSupportCounit l E c S n K =
        (PurCompactSupport.finiteReductionIso l E Y n).hom.app
            ((scalarSupport l E c S).obj K) ≫
          scalarSupportNativeCounit l E c S n K ≫
            (scalarSupportEvaluation l E c S n).hom.app K := by
      unfold scalarSupportCounit scalarSupportProjection
      erw [Adjunction.homEquiv_naturality_right_symm, change_adjunction
        (pbcDerivedScalarAdjunction (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) Y)) (coefficientFiniteAdjunction l E Y n)]
      simp only [Category.assoc]
      rfl
    rw [hfac]
    infer_instance

end WeilConjectures.PurStrictScalar
