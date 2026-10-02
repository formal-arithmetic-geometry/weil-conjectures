/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Smooth

/-!
# Cartier's theorem: group schemes in characteristic zero are smooth

**Cartier's theorem** states that every group scheme locally of finite type over a field `K` of
characteristic zero is reduced, and hence smooth over `K`.

A group scheme over `K` is a scheme `G` with a structure morphism `f : G ⟶ Spec K` making
`Over.mk f` a group object of the category of `K`-schemes, that is, carrying

```
  G ×_{Spec K} G --- mul ---> G <--- one --- Spec K
```

together with an inverse `G ⟶ G`, all of them morphisms over `Spec K`.

Mathlib provides `AlgebraicGeometry.smooth_of_grpObj`: a group scheme locally of finite type over
a field which is *geometrically* reduced is smooth over that field.  In characteristic zero the
base field is perfect, so reducedness and geometric reducedness agree; Mathlib does not yet have
that implication (`Mathlib/AlgebraicGeometry/Geometrically/Reduced.lean` only goes the easy way),
so the smoothness half is stated separately below rather than derived here.

## Main statements

* `AlgebraicGeometry.isReduced_of_grpObj`: a group scheme locally of finite type over a field of
  characteristic zero is reduced.
* `AlgebraicGeometry.smooth_of_grpObj_of_charZero`: such a group scheme is smooth over the base
  field.

## Blueprint

`AlgebraicGeometry.isReduced_of_grpObj` and `AlgebraicGeometry.smooth_of_grpObj_of_charZero`
implement `sk-i-cartier`.

The result is due to Cartier, *Questions de rationalité des diviseurs en géométrie algébrique*
(1958).
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] [CharZero K] {G : Scheme} (f : G ⟶ Spec (.of K))
  [LocallyOfFiniteType f] [GrpObj (Over.mk f)]

/-- A group scheme locally of finite type over a field of characteristic zero has no nilpotents
in its structure sheaf, i.e. it is reduced.
(blueprint: `sk-i-cartier`) -/
theorem isReduced_of_grpObj : IsReduced G := by
  sorry

/-- **Cartier's theorem**: a group scheme locally of finite type over a field of characteristic
zero is smooth over the base field, equivalently `dim Lie(G) = dim G`.
(blueprint: `sk-i-cartier`) -/
theorem smooth_of_grpObj_of_charZero : Smooth f := by
  sorry

end AlgebraicGeometry
