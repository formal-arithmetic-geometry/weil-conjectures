/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftChainPart
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftDerivedPart

/-! # Signed shifts of normalized reindexing comparisons

Source: Stacks 0GMX, 0A8X, 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Signed shifts commute with every product-normalized reindexing comparison.
Source: Stacks 0A8X, 08JA. -/
theorem signed_shift_laws {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
      ShiftLaws l E g s SX SY TX TY c sX sY := by
  obtain ⟨sX, sY, hchain⟩ := chain_shift_part_exists l E g s SX SY TX TY c
  refine ⟨sX, sY, ⟨hchain, ?_⟩⟩
  exact derived_shift_part l E g s SX SY TX TY c

end WeilConjectures.PodReindexingCoherence
