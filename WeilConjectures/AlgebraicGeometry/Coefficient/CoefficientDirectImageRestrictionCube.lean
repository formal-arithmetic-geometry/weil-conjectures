/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedScalarMate.DerivedScalarMateThickLocus

/-! # The ordinary coefficient restriction cube
Source: Stacks Project, Cohomology on Sites, Tags 0D6E and 07A6.
(blueprint: lem-pbc-coefficient-direct-image-restriction-cube).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] proEtaleRingRestrictionDirectImage

end AlgebraicGeometry.Scheme
