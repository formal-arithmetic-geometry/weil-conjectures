/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Prime

/-!
# Graded prime avoidance

Source: Stacks Project, Algebra, Lemma 10.57.6 (Tag 00JS, `algebra-lemma-graded-silly`)
(blueprint: lem-sc-graded-prime-avoidance).
-/

@[expose] public section

universe u v

namespace HomogeneousIdeal

-- A homogeneous ideal contains every homogeneous component of each of its elements.

-- A nonzero homogeneous element in the irrelevant ideal cannot have degree zero.

-- Strong induction, choosing a minimal prime to avoid a separate antichain reduction.

end HomogeneousIdeal
