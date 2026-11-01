/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Elementary changes between generating tuples over a local ring

Source: Stacks Project, Algebra, Tags 00DV (`lemma-NAK`) and 00E9
(`lemma-characterize-local-ring`); the agent-formulated generating-tuple consequence
used in the local-ring reduction of `lem-pur-frame-independence.proof.md`
(blueprint: lem-pur-local-generating-tuples).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped BigOperators

namespace Module

private inductive TupleOp (R : Type u) [CommRing R] (ι : Type) where
  | scale (i : ι) (a : Rˣ)
  | swap (i j : ι) (h : i ≠ j)
  | shear (i j : ι) (a : R) (h : i ≠ j)

private def TupleOp.inv {R : Type u} [CommRing R] {ι : Type} :
    TupleOp R ι → TupleOp R ι
  | .scale i a => .scale i a⁻¹
  | .swap i j h => .swap i j h
  | .shear i j a h => .shear i j (-a) h

section TupleHelpers

variable {R : Type u} [CommRing R] {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
variable {M : Type v} [AddCommGroup M] [Module R M]

omit [DecidableEq ι] in
omit [DecidableEq ι] in
omit [DecidableEq ι] in
omit [DecidableEq ι] in
end TupleHelpers


end Module
