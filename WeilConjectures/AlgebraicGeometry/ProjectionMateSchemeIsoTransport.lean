/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.CategoryTheory.Comma.Arrow
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedQCoh
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedFunctorComparisons

/-! # Projection mate transport along scheme isomorphisms

Source: Stacks Project, Tag 08EU, affine-local reduction, expanded along scheme isomorphisms.
(blueprint: lem-pc-projection-mate-scheme-iso-transport).
-/

@[expose] public section

universe u w w'

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

set_option autoImplicit false

namespace ProjectionMateTransport

end ProjectionMateTransport

end AlgebraicGeometry
