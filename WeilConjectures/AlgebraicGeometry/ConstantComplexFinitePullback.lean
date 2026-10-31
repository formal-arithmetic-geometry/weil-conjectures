/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantComplexStrictBaseChangeData

/-! # Normalized constant-complex comparisons

Source: Stacks Project, Modules on Sites, Tags 03EK, 03EL and 03CZ.
(blueprint: lem-a1-constant-complex-finite-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [-instance] AlgebraicGeometry.Scheme.coefficientProEtaleModelBaseChange_isContinuous
  WeilConjectures.integralOperationsSiteSmall WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify
open scoped ChangeOfRings
namespace AlgebraicGeometry.ConstantComplexBaseChange

/-- The finite constant-complex comparison preserves the actual quotient transitions.
Source: Stacks Project, Modules on Sites, Tags 03EL and 03EK; Sites, Tag 00YV.
(blueprint: lem-a1-constant-complex-finite-pullback).

Proof: Apply the constant-module inverse-image comparison and the sheaf tensor
comparison to each degree and quotient ring. They give a natural isomorphism
sending each pulled constant tensor to the same constant tensor. Naturality gives
commutation with the differential and scalar chain maps. Pull the semilinear finite
transition through the canonical pullback–restriction comparison; its unit equation
sends the pullback of every section m to the pullback of its original transition.
The tensor generator formula and normalized transitions show this map commutes with
the level isomorphisms. The consecutive squares yield the natural isomorphism of
strict towers, with the stated components after scalar restriction. No flatness or
nonempty-site assumption is used. -/
theorem normalized_finite_pullback_exists {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R : Type u} [CommRing R] (I : Ideal R)
    (dY : FiniteTower Y I) (dX : FiniteTower X I)
    (hdY : dY.IsNormalized Y I) (hdX : dX.IsNormalized X I) :
    ∃ f : FiniteComparison g I dY dX, f.IsNormalized g I := by sorry

end AlgebraicGeometry.ConstantComplexBaseChange
