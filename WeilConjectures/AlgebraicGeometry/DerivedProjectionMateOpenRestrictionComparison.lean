/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.OpenRestrictionAdjunctionHomDescent
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTensorCounitDescent
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionQCoh

/-! # Open restriction comparison for derived projection mates

Source: Stacks Project, Tag 08EU, first sentence of the proof, and Tag 08FE.
(blueprint: lem-pc-derived-projection-mate-open-restriction-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry

attribute [local irreducible] schemeDerivedTensorMonoidal HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.mapDerivedCategory DerivedCategory.homologyFunctor

end AlgebraicGeometry
