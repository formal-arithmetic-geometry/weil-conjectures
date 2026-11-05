/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Presentation of derived open-extension mates on complexes

Source: Stacks Project, Tags 08BT and 08BW.
-/

@[expose] public section

universe w vA vB vC uA uB uC

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory.Adjunction

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  {L : B ⥤ A} {R : A ⥤ B} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

end CategoryTheory.Adjunction

end
