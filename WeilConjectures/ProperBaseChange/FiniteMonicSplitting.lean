/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # A simultaneous finite free splitting extension

Source: Stacks Project, Morphisms, Tag 03HW, proof of lemma-massage-finite; Algebra,
lemma-adjoin-roots. Split equations successively and compose their finite free bases
(blueprint: lem-weil-pbc-finite-monic-simultaneous-splitting).
-/

@[expose] public section

universe u

open Polynomial

