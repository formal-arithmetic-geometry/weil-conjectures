/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsSepClosed
public import Weil.Definitions

/-!
# Zariski density of rational points on a smooth scheme

Let `k` be a separably closed field and let `X` be a smooth `k`-scheme, given by a
structure morphism `f : X ⟶ Spec k`. Then the `k`-rational points of `X` are Zariski dense
in `X`.

The reason is that smoothness forces the residue field of a closed point of `X` to be a
separable extension of `k`, hence equal to `k`; since every nonempty open subscheme of `X`
is again smooth over `k` and contains a closed point of some affine open, every nonempty
open of `X` meets `X(k)`. The same argument shows that `X(k)` is nonempty as soon as `X` is,
so no such hypothesis is needed.

The `k`-rational points are `AlgebraicGeometry.Scheme.Hom.fieldPoints f k`, the sections
of `f`, and we record their density as density of the set of underlying points of `X`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints`: the `k`-rational points of a
  smooth scheme over a separably closed field `k` are Zariski dense.
- `AlgebraicGeometry.Scheme.Hom.infinite_fieldPoints`: a smooth proper geometrically integral
  curve over a separably closed field has infinitely many rational points.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- **Zariski density of rational points.** Let `X` be a smooth scheme over a separably closed
field `k`, given by its structure morphism `f : X ⟶ Spec k`. Then the image in `X` of the set
`X(k)` of `k`-rational points is Zariski dense.

(blueprint: `sk-prop-picard-dense-points`) -/
theorem Hom.denseRange_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k))) [Smooth f] :
    DenseRange fun p : f.fieldPoints k ↦ (p.1.base default : X) :=
  sorry

/-- **Infinitude of the rational points of a curve.** A smooth proper geometrically integral
curve over a separably closed field has infinitely many rational points: it is irreducible of
dimension one, so every nonempty open is infinite, and
`AlgebraicGeometry.Scheme.Hom.denseRange_fieldPoints` makes `X(k)` meet all of them.

(blueprint: `sk-prop-picard-dense-points`) -/
theorem Hom.infinite_fieldPoints [IsSepClosed k] (f : X.Hom (Spec (.of k)))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] :
    Infinite (f.fieldPoints k) :=
  sorry

end AlgebraicGeometry.Scheme
