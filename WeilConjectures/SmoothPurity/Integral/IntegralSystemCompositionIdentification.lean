/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # The finite-system compositor is the strict sequence compositor

Source: Stacks 0D6D and 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent finite systems with the positive uniformizer quotients are the strict
quotient systems on the ringed sequence site, and their inverse images are the same
left adjoints of the same sectionwise direct images. Both compositors are the mates of
the sectionwise fibre-product pasting map, hence they agree, before and after
localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite-system adjunction is the universal adjunction of the strict sequence
direct image.
Source: Stacks 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem finiteSystemAdjunction_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteSystemAdjunction (integralSystemRings l E) (integralSystemTransition l E) f =
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f) :
        finiteSystemPullback (integralSystemRings l E) (integralSystemTransition l E) f ⊣
          finiteSystemPushforward (integralSystemRings l E) (integralSystemTransition l E) f) :=
  rfl

set_option trace.profiler true in
set_option maxHeartbeats 1000000 in
-- Comparing the two presentations of the same adjunctions unfolds their module categories.
/-- The finite-system compositor is the strict sequence compositor.
Source: Stacks 0D6D, 03D3
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: both are characterized as the unique mates of the sectionwise fibre-product
pasting isomorphism for the same direct images and adjunctions. -/
theorem finiteSystemComposition_eq {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSequenceComposition l E h k := by
  obtain ⟨d, hd, hs⟩ := (finiteSystemComposition_existsUnique (integralSystemRings l E)
      (integralSystemTransition l E) h k).exists.choose_spec
  have key : conjugateIsoEquiv
      ((finiteSystemAdjunction (integralSystemRings l E) (integralSystemTransition l E) k).comp
        (finiteSystemAdjunction (integralSystemRings l E) (integralSystemTransition l E) h))
      (finiteSystemAdjunction (integralSystemRings l E) (integralSystemTransition l E) (h ≫ k)) =
    conjugateIsoEquiv
      ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)).comp
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))) := by
    rw [finiteSystemAdjunction_eq, finiteSystemAdjunction_eq, finiteSystemAdjunction_eq]
  have hd' := (congrArg (fun e ↦ e (finiteSystemComposition (integralSystemRings l E)
    (integralSystemTransition l E) h k)) key).symm.trans hd
  apply (integralComparisonSequenceComposition_existsUnique l E h k).unique ?_
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  exact ⟨d, hd', hs⟩

set_option trace.profiler true in
set_option maxHeartbeats 1000000 in
-- Rewriting inside the derived compositor unfolds the same module categories.
/-- The derived finite-system compositor is the derived strict sequence compositor.
Source: Stacks 0D6D, 015F
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem finiteSystemDerivedComposition_eq {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :
    finiteSystemDerivedComposition (integralSystemRings l E) (integralSystemTransition l E) h k =
      integralComparisonSystemComposition l E h k := by
  unfold finiteSystemDerivedComposition integralComparisonSystemComposition
  rw [finiteSystemComposition_eq]
  rfl

end WeilConjectures
