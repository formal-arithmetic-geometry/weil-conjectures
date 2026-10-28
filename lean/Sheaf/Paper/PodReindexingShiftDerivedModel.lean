/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Representative model part of the derived signed shift square

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

This module isolates the equation on localized representatives.  The remaining
localization descent is recorded separately.
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

/-- The component equation used in the derived signed shift square. -/
def derivedShiftEquation {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY)
    (M N : podReindexingDerived l E Y s) (a b : ℤ) : Prop :=
  c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      (signedShift l E X s ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) a b).hom =
    (podReindexingDerivedFunctor l E g s).map (signedShift l E Y s M N a b).hom ≫
      ((podReindexingDerivedFunctor l E g s).commShiftIso (b-a)).hom.app
        ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
      (c.derived.hom.app (op M, N))⟦b-a⟧'

/-- The signed shift equation on K-injective localized representatives.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA.
Proof: expand the chosen K-injective representatives in `Comparison.derived_model`,
transport the signed reindexing through the chain shift isomorphisms, and use the
fixed product projections to identify both composites degree by degree. -/
theorem derived_shift_model {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∀ (P I : K l E Y s) (hI : I.IsKInjective) (a b : ℤ),
      derivedShiftEquation l E g s SX SY TX TY c
        ((podReindexingQ l E Y s).obj P)
        ((podReindexingQ l E Y s).obj I) a b := by
  sorry

end WeilConjectures.PodReindexingCoherence
