/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Derived direct image of a degreewise split sequence of K-injectives

Source: Stacks Project, Tags 0152 and 079V
(blueprint: lem-pc-derived-functor-termwise-split-ses-triangle).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

end AlgebraicGeometry.RingedSpace
