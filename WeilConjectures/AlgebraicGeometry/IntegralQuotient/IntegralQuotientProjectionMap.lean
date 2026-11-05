/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

/-! # Integral quotient comparison for unbounded direct image

Source: blueprint main-20261015, integral proper base change proof, paragraphs (1), (3)
(blueprint: def-sfb-integral-quotient-projection-map).

The mate is formed with the actual derived adjunctions. Quotient levels are indexed by
n + 1 and every tensor product is the ordinary, uncompleted derived tensor product.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProEtale.QuotientChange
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale.IntegralQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The perfect-coefficient projection arrow: the recorded module-object projection map
(the counit transpose of the specified derived tensor-pullback comparison followed by the
integral counit), followed by the direct image of the actual cartesian pullback of the
quotient coefficient.
Source: Stacks 0944, 0B56 (blueprint: def-sfb-integral-quotient-projection-map). -/
@[irreducible] def projectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (K : DerivedCategory (Modules (integral l E) X)) :
    (F (integral l E) f).obj K ⊗ B (reduction l E n) Y ⟶
      (F (integral l E) f).obj (K ⊗ B (reduction l E n) X) := by
  have c := coefficientPull l E f n
  unfold L CondensedRing.moduleObjectDerivedPullback at c
  unfold F CondensedRing.moduleObjectDerivedPushforward
  exact CondensedRing.moduleObjectProjectionMap (integral l E) f K
      (B (reduction l E n) Y) ≫
    (CondensedRing.lowerStar (integral l E) f).rightDerivedFunctor.map (K ◁ c)

end AlgebraicGeometry.ProEtale.IntegralQuotient
