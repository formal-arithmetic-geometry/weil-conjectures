/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Existence of the signed chain shift presentations

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: new-pod-reindexing-chain-shift-presentations).

This is the presentation part of the chain-shift argument.  The remaining
reindexing square is recorded separately in
`PodReindexingChainShiftSquare`.
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

/-- Signed Hom-complex shift presentations exist on each of the two sites.

The construction uses the product projections of the Hom complex.  In degree
`r`, the component indexed by `p` is reindexed to `p-a` and multiplied by
`(-1)^(a*r)`.  The ratio of consecutive scalars is the sign in the Hom
 differential, so the projectionwise maps form chain isomorphisms.  This
statement is the first, strictly smaller part of Step 4.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
(blueprint: new-pod-reindexing-chain-shift-presentations). -/
theorem chain_shift_presentations
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∃ (sX : ChainShift l E X s) (sY : ChainShift l E Y s),
      True := by
  sorry

end WeilConjectures.PodReindexingCoherence
