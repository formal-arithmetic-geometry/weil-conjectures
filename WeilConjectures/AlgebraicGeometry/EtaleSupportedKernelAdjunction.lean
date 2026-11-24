/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek

/-!
# The support kernel and the right adjoint of closed etale direct image

## References

* Stacks Project, Tags 09XQ, 04CA

## Main definitions

- `AlgebraicGeometry.Etale.supportedKernel`: the kernel of the open adjunction unit.
- `AlgebraicGeometry.Etale.supportedClosedInverseImage`: its inverse image on the closed part.

## Main statements

- `AlgebraicGeometry.Etale.supportedKernel_closedAdjunction`: the canonical supported unit is
  invertible, closed direct image is exact, and supported inverse image is its right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The functor `P_Z(F) = ker(F → j_*j⁻¹F)`, formed as the kernel of the adjunction unit
in the functor category. Limits of functors are computed pointwise, so its value is the
kernel in abelian etale sheaves, with its canonical action on morphisms (Stacks, Tag 09XQ). -/
noncomputable def supportedKernel {O X : Scheme.{u}} (j : O ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit

end AlgebraicGeometry.Etale
