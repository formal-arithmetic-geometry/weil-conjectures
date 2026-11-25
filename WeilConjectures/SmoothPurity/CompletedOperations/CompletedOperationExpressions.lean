/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-! # Finite typed expressions in tensor and inverse image

Finite typed expressions built from inputs, units, tensor products and inverse images, with
their output scheme as a type index, together with simultaneous substitution.
-/

@[expose] public section
set_option autoImplicit false
universe t s i j
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CompletedOperations

/-- Finite expressions, with their output scheme as a type index. Inputs may occur
repeatedly; no input or scheme index set is required to be finite or nonempty. -/
inductive Expression {S : Type s} (W : S → Scheme.{t}) {I : Type i} (location : I → S) :
    S → Type (max t s i) where
  | input (i : I) : Expression W location (location i)
  | unit (a : S) : Expression W location a
  | tensor {a : S} (P Q : Expression W location a) : Expression W location a
  | pullback {a b : S} (f : W a ⟶ W b) (P : Expression W location b) :
      Expression W location a

/-- Simultaneous capture-free substitution, preserving the scheme type at each input. -/
def Expression.substitute {S : Type s} {W : S → Scheme.{t}}
    {I : Type i} {J : Type j} {location : I → S} {location' : J → S}
    (σ : ∀ i : I, Expression W location' (location i)) {a : S} :
    Expression W location a → Expression W location' a
  | .input i => σ i
  | .unit a => .unit a
  | .tensor P Q => .tensor (P.substitute σ) (Q.substitute σ)
  | .pullback f P => .pullback f (P.substitute σ)

end WeilConjectures.CompletedOperations
