/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteRingTorsorAssociatedModule
import all WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective
import WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Pullback and coefficient comparisons for finite-ring associated module sheaves

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS
(blueprint: lem-weil-pbc-finite-ring-torsor-module-comparisons).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

end AlgebraicGeometry.Scheme.GaloisCover
