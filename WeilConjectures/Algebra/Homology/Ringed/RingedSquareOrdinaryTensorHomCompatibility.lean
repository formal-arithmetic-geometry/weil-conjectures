/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareModuleTensorCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorTotalComponent

/-! # The hom-oriented ordinary total tensor square

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

end SheafOfModules
