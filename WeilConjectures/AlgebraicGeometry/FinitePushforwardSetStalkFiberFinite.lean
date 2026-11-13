/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- The geometric fibre of a finite morphism over an algebraically closed field is finite.

(Stacks, Tag 03QP) -/
theorem finite_pushforward_set_stalk_fiber_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite {x : Spec (.of Ω) ⟶ X // x ≫ f = y} := by
  exact @Scheme.Hom.GeometricFiber.finite _ _ f Ω _ y _
end AlgebraicGeometry
