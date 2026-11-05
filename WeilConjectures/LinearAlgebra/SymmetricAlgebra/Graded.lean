/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.LinearAlgebra.TensorAlgebra.Grading

/-!
# The grading of the symmetric algebra

Source: Stacks Project, Algebra, Section 00DM, tensor algebra
(blueprint: lem-weil-pbc-symmetric-algebra-graded).
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

open scoped DirectSum Pointwise

end SymmetricAlgebra
