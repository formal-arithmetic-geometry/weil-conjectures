/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Restriction of scalars along an isomorphism preserves K-flatness

Source: Stacks Project, Tags 06YN and 03ER.

Restricting the unit along an isomorphism of ring sheaves gives the unit, which is flat, so
`SheafOfModules.isKFlat_restrictScalars_of_flat` applies.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{max u v} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J AddCommGrpCat.{max u v}]
  {R B : Sheaf J CommRingCat.{max u v}}

end SheafOfModules
