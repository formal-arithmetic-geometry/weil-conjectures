/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Cartier's theorem: group schemes in characteristic zero are reduced

**Cartier's theorem** states that every group scheme locally of finite type over a field `K`
of characteristic zero is reduced, and hence smooth. This file states the reducedness half,
which is the part not yet available in Mathlib.

Mathlib already provides the other half: `AlgebraicGeometry.smooth_of_grpObj` says that a
group scheme locally of finite type over a field which is *geometrically* reduced is smooth
over that field. In characteristic zero the base field is perfect, so reducedness and
geometric reducedness agree; consequently, once
`AlgebraicGeometry.isReduced_of_grpObj_of_charZero` below is available, the smoothness
statement of the blueprint subsection — `Smooth f`, equivalently `dim Lie(G) = dim G` — is a
formal consequence of `AlgebraicGeometry.smooth_of_grpObj` and needs no separate theorem.
That is why only reducedness is stated here.

## Main statements

- `AlgebraicGeometry.isReduced_of_grpObj_of_charZero`: a group scheme locally of finite type
  over a field of characteristic zero is reduced.

The result is due to Cartier, *Questions de rationalité des diviseurs en géométrie
algébrique* (1958).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Blueprint `sk-i-cartier`: Characteristic-zero group smoothness. A group scheme locally of
finite type over a field of characteristic zero has no nilpotents in its structure sheaf, i.e.
it is reduced; combined with `AlgebraicGeometry.smooth_of_grpObj` this gives Cartier's theorem
that such a group scheme is smooth over the base field. -/
theorem isReduced_of_grpObj_of_charZero {K : Type u} [Field K] [CharZero K] {G : Scheme}
    (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [GrpObj (Over.mk f)] : IsReduced G := by
  sorry

end AlgebraicGeometry
