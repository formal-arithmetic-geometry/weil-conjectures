/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower

/-! # The Shrink coefficient model in the common-stage point cohomology square

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

attribute [local instance 2000] HasDerivedCategory.ofIsGrothendieckAbelian

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (Stage inclusion)

end WeilConjectures
