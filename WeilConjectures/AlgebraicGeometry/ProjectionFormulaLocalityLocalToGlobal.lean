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
import WeilConjectures.Topology.SheafIsomorphismLocalOpenCover

/-! # Projection formula locality: local to global

If the projection-formula map is an isomorphism after restriction to every member of an open
cover, it is an isomorphism (Stacks Project, Lemma 36.22.1, Tag 08EU). -/

@[expose] public section
universe u w v
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
set_option autoImplicit false
namespace AlgebraicGeometry
variable {X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
end AlgebraicGeometry
