/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.Algebra.Category.ModuleCat.Sheaf.HomModule
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # Global functions acting on derived morphisms

Source: Stacks Project, Derived Categories of Schemes, Tag 08EJ
(blueprint: def-sc-derived-global-scalar).
-/

universe v z

open CategoryTheory

namespace AlgebraicGeometry

/-- Multiply a derived morphism by a global function, encoded as a compatible family of
local sections. The action on module sheaves is sectionwise multiplication, and the action
on the derived category is its canonical localization via Mathlib's derived linear structure.
Source: Stacks Project, Tag 08EJ (blueprint: def-sc-derived-global-scalar). -/
noncomputable def schemeDerivedScalar
    (X : Scheme.{v})
    [HasDerivedCategory.{z} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    {E E' : schemeDerivedCategory X}
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{v}))
    (α : E ⟶ E') : E ⟶ E' :=
  letI : Linear
      (RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{v}))
      (SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.homLinear X.sheaf.obj (moduleRings X.toRingedSpace).property
  f • α

end AlgebraicGeometry
