/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Finiteness.Lattice

/-! # Simultaneous finite free surjections after scalar extension

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent,
the finite family of generators before cone-cycle attachment.
(blueprint: lem-sc-finite-scalar-surjections).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

end ModuleCat
