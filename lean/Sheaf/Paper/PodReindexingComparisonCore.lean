/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Core comparison data for reindexing

Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-comparison-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The normalized tensor and Hom comparison data exists for reindexing along a scheme
isomorphism.  This is the construction of all fields of `Comparison`, before the
evaluation equation is imposed.

Source: blueprint dual-Tate compatibility, Steps 1 and 2; Stacks 0GMX and 0A8X
(blueprint: lem-pod-reindexing-comparison-core).

Proof: combine the product-Hom comparison and derived resolution model with the
sectionwise tensor comparison.  Totalize the pure-tensor maps, descend them through
the localization on independent K-flat representatives, and use the recorded
K-injective model equations.  The resulting maps satisfy every field of
`Comparison`, including the projection and model normalizations.
-/
theorem comparison_core_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    Nonempty (Comparison l E g s SX SY TX TY) := by
  sorry

end WeilConjectures.PodReindexingCoherence
