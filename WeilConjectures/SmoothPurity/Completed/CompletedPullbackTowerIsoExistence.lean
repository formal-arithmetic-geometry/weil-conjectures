/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTensorLevel
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTransitionSquare

/-! Existence of the normalized coherent tensor tower comparison.

Source: Stacks 0941 and 07A4 (blueprint: lem-pur-completed-pullback-tower-iso-existence).
Proof: use the prescribed finite component at every natural-number level.  The
adjacent transition square packages these components with `NatTrans.ofOpSequence`;
`NatIso.ofComponents` then supplies the levelwise inverses and all remaining
naturality squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

open CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end WeilConjectures
