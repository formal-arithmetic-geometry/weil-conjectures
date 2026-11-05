/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exactness on a graded piece of a symmetric algebra

Source: Stacks Project, Algebra, Lemma 00DO (blueprint: lem-weil-pbc-symmetric-degree-exact).
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

open scoped TensorProduct

end SymmetricAlgebra
