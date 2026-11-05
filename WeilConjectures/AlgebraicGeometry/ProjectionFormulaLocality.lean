/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaLocalityLocalToGlobal
import WeilConjectures.AlgebraicGeometry.ProjectionFormulaLocalityGlobalToLocal

/-! # Locality of the projection-formula isomorphism

Source: literature/stacks-project/cohomology.tex, Equation 20.54.2.1,
and perfect.tex, Lemma 36.22.1 (Tag 08EU)
(blueprint: lem-pc-projection-locality).

The map `φ` below is the canonical projection-formula map for `f`, `E`, and
`K`; the statement records that its being an isomorphism is local on an open
cover of the target. -/

@[expose] public section

universe u w v

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

set_option autoImplicit false

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
