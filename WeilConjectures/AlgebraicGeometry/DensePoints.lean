/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import Weil.Definitions

@[expose] public section

/-!
# Zariski density of rational points on a smooth scheme

Let `k` be a separably closed field and let `X` be a smooth `k`-scheme, given by a
structure morphism `f : X ⟶ Spec k`, which has at least one `k`-rational point. Then the
`k`-rational points of `X` are Zariski dense in `X`.

The reason is that smoothness forces the residue field of a closed point of `X` to be a
separable extension of `k`, hence equal to `k`; since every nonempty open subscheme of `X`
is again smooth over `k` and contains a closed point of some affine open, every nonempty
open of `X` meets `X(k)`.

The `k`-rational points are `AlgebraicGeometry.Scheme.Hom.fieldPoints f k`, the sections
of `f`, and we record their density as density of the set of underlying points of `X`.

As a special case, a smooth projective curve over a separably closed field has infinitely
many rational points, since a curve is irreducible of dimension one and hence has
infinitely many points in every nonempty open.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.dense_range_fieldPoints`: the `k`-rational points of a
  smooth scheme over a separably closed field `k` are Zariski dense, provided there is at
  least one of them.
-/

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- Blueprint `sk-prop-picard-dense-points`: Zariski density of rational points.

Let `X` be a smooth scheme over a separably closed field `k`, given by its structure
morphism `f : X ⟶ Spec k`, and assume that `X` has a `k`-rational point. Then the image
in `X` of the set `X(k)` of `k`-rational points is Zariski dense.

In particular, for a smooth projective curve `X` over a separably closed field `k` with
`X(k) ≠ ∅`, the set `X(k)` is infinite. -/
theorem Hom.dense_range_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k))) [Smooth f]
    (hne : Nonempty (f.fieldPoints k)) :
    Dense (Set.range fun p : f.fieldPoints k ↦ (p.1.base default : X)) :=
  sorry

end AlgebraicGeometry.Scheme
