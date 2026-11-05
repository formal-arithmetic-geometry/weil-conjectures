/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarOperationComp
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Constructible restriction and rationalization of scalar comparisons

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-constructible-operation-restriction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme

-- `SignedDoubleHomCone.moduleBinaryBiproducts` leaves its universe free
attribute [-instance] CategoryTheory.SignedDoubleHomCone.moduleBinaryBiproducts
section ConditionalRestriction
variable {X Y : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
variable (d : AdicCoefficientDatum A) (H : PbcCompletedDerived X d ⥤ PbcCompletedDerived Y d)
variable (h : ∀ K : PbcBoundedConstructibleComplete X d,
  PbcIsBoundedConstructibleComplete Y d (H.obj K.obj))

end ConditionalRestriction

section ConditionalOperations
variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
variable [Algebra (Padic l) E] [Algebra (Padic l) F]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable (i : E →ₐ[Padic l] F) {X Y : Scheme.{u}} (g : X ⟶ Y)

variable [IsNoetherian X] [IsNoetherian Y]
variable (dX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
variable (dY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
variable (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
variable (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))

attribute [-instance] ULift.module
attribute [local irreducible] pbcRationalScalarHom

end ConditionalOperations
end AlgebraicGeometry.Scheme
