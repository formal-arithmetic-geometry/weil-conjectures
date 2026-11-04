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
