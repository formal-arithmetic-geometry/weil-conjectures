/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.PrimitiveCounitEvaluation

/-! # Section and unit calculus for ordinary finite evaluation

Source: Stacks Project, Tags 03D3 and 03D8, and the unit normalization in
PrimitiveCounitEvaluation. These proved calculations keep section transports and
chosen-adjunction conversions outside the compositor calculation.
(blueprint: lem-pur-ordinary-pullback-evaluation-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
namespace WeilConjectures.PullbackCompositionTransport.EvaluationCalculus

private theorem eqToIso_app_section_heq
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {F G : D ⥤ SheafOfModules R}
    (e : F = G) (N : D) (U : Cᵒᵖ) :
    HEq (fun x ↦ ((eqToIso e).hom.app N).val.app U x)
      (fun x : (F.obj N).val.obj U ↦ x) := by
  subst G
  rfl

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] PrimitiveCounit.inverseEvaluation
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback
attribute [local irreducible] Padic constantSheaf presheafToSheaf
  Scheme.coefficientProEtaleDirectRingMap
attribute [local implicit_reducible] integralCoefficientSheaf
  integralOperationsLevelPullback integralComparisonSequencePullback
  coefficientSequenceEvaluation integralComparisonSequenceDirectImage
  Scheme.coefficientProEtaleModuleDirectImage PrimitiveCounit.inverse
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' ModuleCat.RestrictScalars.map'

/-- The primitive and integral presentations of system direct image agree.
Source: Stacks 03D7; unfold their common sectionwise pushforward construction.
(blueprint: lem-pur-ordinary-pullback-evaluation-calculus). -/
theorem direct_eq {X Y : Scheme.{t}} (f : X ⟶ Y) :
    PrimitiveCounit.direct l E f = integralComparisonSequenceDirectImage l E f := by
  rfl

/-- Direct image commutes with finite evaluation as an equality of functors.
Source: Stacks 03D7; rewrite the primitive direct-evaluation equality by `direct_eq`.
(blueprint: lem-pur-ordinary-pullback-evaluation-calculus). -/
theorem directEvaluation_eq {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))) := by
  rw [← direct_eq]
  exact PrimitiveCounit.directEvaluation_eq l E f n

/-- The identity comparison determined by the proved direct-evaluation equality.
Source: Stacks 03D7 (blueprint: lem-pur-ordinary-pullback-evaluation-calculus). -/
@[irreducible] def directEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :=
  eqToIso (directEvaluation_eq l E f n)

attribute [local irreducible] PrimitiveCounit.direct PrimitiveCounit.ringMap
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

/-- The chosen primitive evaluation satisfies its defining unit normalization.
Source: Stacks 03D3 and PrimitiveCounitEvaluation. Unfold the chosen evaluation and
specialize the first conjunct of its unique-witness specification at the system M.
(blueprint: lem-pur-ordinary-pullback-evaluation-calculus). -/
theorem primitiveEvaluationUnit {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) :
    (coefficientSequenceEvaluation l E Y n).map
        ((Adjunction.ofIsRightAdjoint (PrimitiveCounit.direct l E f)).unit.app M) ≫
      (eqToIso (PrimitiveCounit.directEvaluation_eq l E f n)).hom.app
        ((PrimitiveCounit.inverse l E f).obj M) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).map
            ((PrimitiveCounit.inverseEvaluation l E f n).hom.app M) =
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
          ((coefficientSequenceEvaluation l E Y n).obj M) := by
  unfold PrimitiveCounit.inverseEvaluation
  exact (PrimitiveCounit.inverseEvaluation_existsUnique l E f n).choose_spec.1 M

/-- The direct-evaluation comparison is the identity on underlying sections.
Source: Stacks 03D7. Equality elimination makes `eqToIso` act heterogeneously as
identity on every section; `congr_heq` specializes this to x. Both section carriers
are the same carrier of the original module. This includes n=0 and arbitrary
transition maps.
(blueprint: lem-pur-ordinary-pullback-evaluation-calculus). -/
theorem directEvaluation_apply {X Y : Scheme.{t}} (f : X ⟶ Y)
    (n : ℕ) (N : coefficientSequenceModules l E X) (U : Y.ProEt)
    (x : ((integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))) :
    ((directEvaluation l E f n).hom.app N).val.app (op U) x = x := by
  unfold directEvaluation
  exact congr_heq
    (eqToIso_app_section_heq (R := integralCoefficientSheaf l E Y n)
      (directEvaluation_eq l E f n) N (op U)) (HEq.refl x)


end WeilConjectures.PullbackCompositionTransport.EvaluationCalculus
