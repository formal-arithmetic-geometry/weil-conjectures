/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.Tower

/-!
# Separable tensor purely inseparable field extensions

Source: literature/stacks-project/algebra.tex, Lemma Tag 07QH (blueprint:
lem-weil-pbc-separable-tensor-purely-inseparable-field)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

