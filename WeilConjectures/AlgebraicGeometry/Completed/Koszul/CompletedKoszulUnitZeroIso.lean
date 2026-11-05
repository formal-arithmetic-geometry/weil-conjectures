/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicKoszulConstruction
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence

/-! # The degree-zero completed Koszul unit is invertible

Source: Stacks Project, Tag 099M, the finite Koszul construction; Tag 03EK,
scalar extension of module sheaves.
(blueprint: lem-weil-pbc-completed-koszul-unit-zero-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
