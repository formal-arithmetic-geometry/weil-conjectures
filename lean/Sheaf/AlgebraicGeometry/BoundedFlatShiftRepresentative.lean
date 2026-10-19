/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-! The bounded-flat representative predicate retained after retiring the old
normalization theorem. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Bounded-above flat complex presentations, including their one-fold translates.
Source: Stacks Tag 06YS (blueprint: def-sc-bounded-flat-shift-representative). -/
def boundedFlatShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) ∧
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)

end AlgebraicGeometry
