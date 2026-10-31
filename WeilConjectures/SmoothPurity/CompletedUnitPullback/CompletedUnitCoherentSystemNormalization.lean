/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData
public import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitSystemPullbackUnitNormalization
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitCoherentReductionCompatibility

/-! # Ring-unit normalization of the reduced coherent tensor-unit arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedUnitPullback

/-- The uniquely coherent integral unit arrow reduces to the normalized ring-unit arrow.

Source: Stacks 07A4 and 0941; the coefficient-unit calculation in Step 2
of lem-pur-completed-unit-common-tensor-unitor.
(blueprint: lem-pur-completed-unit-coherent-system-normalization).

Proof: on the regular sequence-site module, ordinary pullback of the tensor
left and right unitors commutes with the pullback tensor comparison. The
calculation is on pure tensors: x tensor a maps to x times the structural
image of a, and the adjunction unit inserts one. The equations survive the
K-flat total tensor construction and derived localization. Transport through
the normalized tensor-Hom left-adjoint comparisons defining tensorSystemUnit;
this proves both unitor equations for tensorSystemPullbackUnit. Lift its
conjugate by the pullback reduction comparison and the two effective unit
counits through fully faithful integralSystemReduction. The reduction/tensor
square transports the two unitor equations to integral objects. Uniqueness
in pullbackTensorIntegralUnitCoherence identifies the lift with the selected
integral arrow. Applying reduction and cancelling its unit counits gives the
displayed equation. This argument uses no completed regular coefficient
object or Core data, and covers different source and target schemes. -/
theorem completedUnit_coherent_tensorSystemReduction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    let V := pullbackTensorIntegralUnit l E Y
    let eY := pullbackTensorIntegralUnitReduction l E Y
    let eX := pullbackTensorIntegralUnitReduction l E X
    let ε := (pullbackTensorIntegralUnitCoherence l E f).exists.choose
    (pullbackTensorCalculus l E X).reduction.map ε.hom.hom ≫ eX.hom =
      (pullbackTensorIntegralReductionPullback l E f V).hom ≫
        (pullbackTensorSequenceDerived l E f).map eY.hom ≫
          (tensorSystemPullbackUnit l E f).hom := by
  have h := completedUnit_coherentReduction_compatibility l E f
  have hn := completedUnit_systemPullbackUnit_normalization l E f
  dsimp only at h ⊢
  rw [hn] at h
  exact h

end WeilConjectures.CompletedUnitPullback
