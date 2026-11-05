/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulAdjoinGenerator

/-! # The algebraic exterior-to-tensor comparison

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-exterior-negative-koszul-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
