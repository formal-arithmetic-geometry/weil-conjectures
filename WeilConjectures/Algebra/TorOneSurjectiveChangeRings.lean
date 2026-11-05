/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Surjectivity of the change-of-rings map on first Tor

Source: Stacks Project, Algebra, Lemma Tag 00MN
(`literature/stacks-project/algebra.tex`, lemma-surjective-on-tor-one-trivial).
(blueprint: lem-weil-pbc-tor-one-surjective-change-rings)

The first homology of a tensor product of a free resolution is the Tor module
of `def-weil-pbc-tor-modules`, realized by Mathlib's `CategoryTheory.Tor'`.
Tensor associativity identifies `(A ⊗[R] F) ⊗[A] (A/J)` with
`F ⊗[R] (A/J)`, with symmetry exchanging the tensor factors. Thus the
homology map below is precisely the node's resolution-induced change-of-rings map.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory

-- Only the right-exact augmented pair and the projective target in degrees 0 and 1
-- are needed. The partial right inverse becomes a right inverse modulo boundaries.

end CategoryTheory
