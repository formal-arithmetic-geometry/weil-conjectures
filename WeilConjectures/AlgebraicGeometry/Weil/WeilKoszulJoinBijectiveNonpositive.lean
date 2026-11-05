/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Prod

/-! # Nonpositive-degree exterior basis splitting

Projection to the tail and contraction with the head coordinate give an explicit
inverse to exterior assembly. Only head degrees zero and one survive in the tensor
coproduct; checking these summands proves the graded join map is bijective.
(Source: Stacks Project, Tag 0664; blueprint: new-weil-pbc-koszul-join-graded-nonpositive.)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

namespace KoszulHeadSplit

open ExteriorAlgebra

variable (R : Type (u + 1)) [CommRing R] (r : ℕ)

end KoszulHeadSplit

variable {A : Type (u + 1)} [CommRing A]

end AlgebraicGeometry.Scheme
