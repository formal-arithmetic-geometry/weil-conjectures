/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplexExtension
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenExtensionGoodComplexPullback

/-! # Good representatives under completed-ring open extension

## References

* [Stacks, Tag 03DI]
* [Stacks, Tag 03DJ]
* [Stacks, Tag 0E8I]
* [Stacks, Tag 0G7E]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

local instance goodOpen_additive {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).Additive :=
  (PurCompactSupport.openAdjunction (PurCompactSupport.completed l E) j).left_adjoint_additive

/-- Completed-ring open extension and its restriction preserve good representatives. -/
theorem openExtension_goodComplex {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    integralOperationsGoodComplex l E Y
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
           (.up ℤ)).obj P.obj) ∧
      integralOperationsGoodComplex l E X
        (((integralOrdinaryPull l E j).mapHomologicalComplex (.up ℤ)).obj
          (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapHomologicalComplex
             (.up ℤ)).obj P.obj)) := by
  exact ⟨openExtension_goodComplex_extension l E j P,
    openExtension_goodComplex_pullback l E j P⟩

end WeilConjectures.IntegralSystemRealization
