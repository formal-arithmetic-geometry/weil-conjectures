/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedTotalTensorExact
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# The exact comparison for a specified total left derived functor

Source: Stacks, derived.tex, Tag 015F.

The comparison is expressed in terms of its universal counit. This accepts both the
total-tensor implementation and the module-object implementation, without requiring their
K-flat interfaces to coincide.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical comparison `LF ≅ D(F)` for the specified total left derived functor
with its universal counit. Source: Stacks Tag 015F.

Exactness makes `mapDerivedCategoryFactorsh` an invertible universal counit. Uniqueness
of left derived functors compares it with the given universal counit. This is the same
`leftDerivedUnique` construction as both existing K-flat comparison interfaces. -/
def leftDerivedExactComparison (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] :
    LF ≅ F.mapDerivedCategory :=
  leftDerivedUnique F.mapDerivedCategory LF ε F.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end CategoryTheory.Functor
