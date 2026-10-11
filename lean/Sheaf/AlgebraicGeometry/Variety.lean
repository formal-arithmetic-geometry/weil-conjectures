/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.Dimension

/-!
# Varieties and curves over a field

Source: the blueprint of the Weil conjectures, chapter `sec-abelian-varieties`, unit
`sk-def-av-jacobian`, node order 453 (blueprint: def-pc-curve); Stacks Project, Varieties,
Definition 33.3.1 (Tag 020D) and Definition 33.43.1 (Tag 0A23).

A `k`-scheme is given, as in `WeilConjectures.AlgebraicGeometry.Curve` (`IsCurve`), by its
structure morphism `f : X ⟶ Spec (.of k)`. "Of finite type" is `LocallyOfFiniteType f` together
with `QuasiCompact f`, Mathlib having no bundled class for the conjunction.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsVariety`: `X` is integral and `f` is separated and of finite
  type (Stacks, Tag 020D).
* `AlgebraicGeometry.Scheme.Hom.IsCurveOverField`: a variety over `k` of dimension exactly one
  (Stacks, Tag 0A23).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- (blueprint: def-pc-curve) A *variety over a field `k`*: a `k`-scheme `X`, with structure
morphism `f : X ⟶ Spec k`, such that `X` is integral and `f` is separated and of finite type,
i.e. locally of finite type and quasi-compact (Stacks, Tag 020D). -/
class Scheme.Hom.IsVariety (f : X ⟶ Spec (.of k)) : Prop
    extends IsSeparated f, LocallyOfFiniteType f, QuasiCompact f where
  /-- The scheme `X` of a variety is integral. -/
  isIntegral : IsIntegral X

/-- (blueprint: def-pc-curve) A *curve over a field `k`*: a variety over `k`
(`Scheme.Hom.IsVariety`) whose dimension `Scheme.dim X` (def-pc-dimension) is exactly `1`
(Stacks, Tag 0A23).

This differs from `AlgebraicGeometry.IsCurve` (`WeilConjectures.AlgebraicGeometry.Curve`,
blueprint def-sc-curves), which asks only that `f` be separated and of finite type and that
`topologicalKrullDim X ≤ 1`: there `X` need not be integral (it may be empty, reducible or
nonreduced), its dimension may be `0`, and the blueprint takes `k` algebraically closed. -/
class Scheme.Hom.IsCurveOverField (f : X ⟶ Spec (.of k)) : Prop extends f.IsVariety where
  /-- A curve has dimension exactly one. -/
  dim_eq_one : X.dim = 1

end AlgebraicGeometry
