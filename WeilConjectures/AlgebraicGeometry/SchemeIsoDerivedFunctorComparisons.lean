/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Functor comparisons across a scheme-isomorphism square

Source: Stacks Project, Tag 08EU, affine-local reduction, expanded by the
K-flat and K-injective constructions of Tags 06YI and 079V.
(blueprint: lem-pc-scheme-iso-derived-functor-comparisons).
-/

@[expose] public section

universe u w w'
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
set_option autoImplicit false

end AlgebraicGeometry
