/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.PodReindexingShiftDerivedModel

/-! # Localization descent for the derived signed shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

The representative equation is extended from K-injective localized objects to
all objects of the derived category.
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

/-- Descent of the representative signed-shift equation through localization.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: resolve the target object by a K-injective complex and represent the
source by a localized complex.  Apply naturality of the comparison and the
K-injective factorization in `Comparison.derived_model`; the representative
hypothesis supplies the signed square on the resulting pair.  Cancel the
isomorphisms from the chosen resolutions and use essential surjectivity of the
localization to obtain the equation for arbitrary derived objects. -/
theorem derived_shift_descent {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (hmodel : ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c
        ((podReindexingQ l E Y s).obj P)
        ((podReindexingQ l E Y s).obj I) a b) :
    ∀ (M N : podReindexingDerived l E Y s) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c M N a b := by
  sorry

end WeilConjectures.PodReindexingCoherence
