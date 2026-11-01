/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitInclusionPullbackData
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence

/-! # The common-stage coherent unit arrow in integral coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

/-- The common-stage unit arrow is the specified image of the integral coherent unit arrow.

Source: Stacks 07A4 and 0941; blueprint common-stage coefficient convention;
Step 4 of lem-pur-completed-unit-common-tensor-unitor.
(blueprint: lem-pur-completed-unit-common-stage-normalization).

Proof: rationalize the uniquely coherent integral unit arrow. The pure-tensor
map formulas for rational pullback and tensor, and the normalized rational
unitor formulas, transport its two unitor laws. Rational unit uniqueness
therefore identifies it with the selected rational unit arrow. At the least
coefficient field include this arrow and conjugate by the specified pullback
object comparison. For an arbitrary common-stage object enlarge the field to
contain its tensor representatives. Scalar-unit normalization, naturality of
the scalar pullback and tensor comparisons, and their cocycles turn both
unit equations into the rational equations at the enlarged stage. Thus the
included arrow satisfies both common-stage laws; common-stage uniqueness
identifies it with the selected arrow. The two natural object comparisons
are exactly tensorInclusionPullbackComparison, so no arbitrary boundary
isomorphism remains. The identity coefficient extension and the empty scheme
satisfy the same formulas. No regular coefficient object or Core data occurs. -/
theorem completedUnit_commonStage_normalization
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
      (Padic.finiteCoefficientBase l Ω)
    let V := pullbackTensorIntegralUnit l E Y
    let εI := (pullbackTensorIntegralUnitCoherence l E f).exists.choose
    let ε := (pullbackTensorCommonStageUnitCoherence l Ω f).exists.choose
    ε.hom = (tensorInclusionPullbackComparison l Ω f).hom.app V ≫
      (tensorUnitInclusion l Ω X).map εI.hom := by sorry

end WeilConjectures.CompletedUnitPullback
