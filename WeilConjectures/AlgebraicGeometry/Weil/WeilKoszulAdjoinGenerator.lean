/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijective
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinLeibniz

/-! # Adjoining one generator to an exterior Koszul complex

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-koszul-adjoin-generator).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

end AlgebraicGeometry.Scheme
