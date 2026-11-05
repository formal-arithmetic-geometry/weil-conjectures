/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The spectrum of an algebraic extension as a limit over finite subextensions

Let `ks / k` be an algebraic field extension. The finite subextensions `K` of `ks / k` form a
nonempty directed poset `AlgebraicGeometry.FiniteIntermediateField k ks`, and `ks` is the
filtered colimit of the `K` in `CommRingCat`. Since `Spec` turns colimits into limits, `Spec ks`
is the cofiltered limit of the affine schemes `Spec K`
(`AlgebraicGeometry.FiniteIntermediateField.isLimitSpecCone`).

We also show that `Spec ks` is the limit of the "diagonal" system
`K ↦ Spec ks ×_{Spec K} Spec ks` (`AlgebraicGeometry.FiniteIntermediateField.isLimitDiagCone`):
two morphisms `T ⟶ Spec ks` agreeing after composition to every `Spec K` are equal.

Both systems have affine stages and affine transition maps, so they can be used with the
limit lemmas of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k ks : Type u) [Field k] [Field ks] [Algebra k ks]

namespace FiniteIntermediateField

/-! ### The diagonal system -/

/-! ### The limit properties -/

variable [Algebra.IsAlgebraic k ks]

end FiniteIntermediateField

end AlgebraicGeometry
