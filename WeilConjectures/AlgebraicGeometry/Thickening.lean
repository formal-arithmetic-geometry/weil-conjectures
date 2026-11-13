/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Thickenings of schemes

For any of the predicates below, a thickening over `S` additionally has
`[T.Over S]`, `[T'.Over S]`, and `[i.IsOver S]`. A thickening of affine
schemes additionally has `[IsAffine T]` and `[IsAffine T']`.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A thickening is a closed immersion
surjective on underlying points. -/
def IsThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ Surjective i

/-- A first order thickening is a closed
immersion whose defining ideal sheaf has square zero. The ideal sheaf is `i.ker` on `T'`. -/
def IsFirstOrderThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ 2 = ⊥

/-- An `n`th order thickening is a
closed immersion whose defining ideal sheaf has `(n + 1)`st power zero. -/
def IsNthOrderThickening {T T' : Scheme.{u}} (n : ℕ) (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥

/-- A finite order thickening is a
closed immersion whose defining ideal sheaf is nilpotent: its `(n + 1)`st
power is zero for some `n : ℕ`. -/
def IsFiniteOrderThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  ∃ n : ℕ, IsNthOrderThickening n i

end AlgebraicGeometry
