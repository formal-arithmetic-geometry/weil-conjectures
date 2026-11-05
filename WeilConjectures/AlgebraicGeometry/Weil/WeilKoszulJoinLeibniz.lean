/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded

/-! # The contraction formula on a head-tail tensor summand

Source: Stacks Project, More on Algebra, Tags 0622 and 0664.
(blueprint: lem-weil-pbc-koszul-join-summand-leibniz).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

end AlgebraicGeometry.Scheme
