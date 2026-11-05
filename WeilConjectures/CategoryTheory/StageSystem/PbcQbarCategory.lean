/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCommonStageCones
public import WeilConjectures.CategoryTheory.StageSystem.PbcVerdierAxioms
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.CategoryTheory.Linear.Basic
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStagePairCategory

/-! # Scalar multiplication on finite-stage morphism classes

Source: blueprint `def-weil-pbc-qbar-category`, scalar-action formula
(blueprint: def-weil-pbc-qbar-category).

The generic quotient construction is specialized below to the actual rational
finite coefficient stages and their canonical derived scalar-extension system.

## Main definitions

* `AlgebraicGeometry.Scheme.pbcQbarCategory` is the finite-stage pair category.
* `CategoryTheory.StageSystem.qbarScalarHom` is its common-stage scalar action.
* `AlgebraicGeometry.Scheme.pbcQbarLinear` supplies the resulting linear structure.
* `AlgebraicGeometry.Scheme.pbcQbarTriangulated` retains the common-stage Verdier structure.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w u v

open CategoryTheory

namespace CategoryTheory.StageSystem

variable (l : ℕ) [Fact l.Prime] (Qbar : Type w) [Field Qbar] [Algebra ℚ_[l] Qbar]
  [qbarClosure : IsAlgClosure ℚ_[l] Qbar]
variable {C : Padic.FiniteCoefficientFields l Qbar → Type u}
  [∀ E, Category.{v} (C E)] [∀ E, Preadditive (C E)] [∀ E, Linear E.val (C E)]
  (S : StageSystem C) [IsDirectedOrder (Padic.FiniteCoefficientFields l Qbar)]

section Linear
variable [transitionAdditive : ∀ {E F : Padic.FiniteCoefficientFields l Qbar}
    (h : E ≤ F), (S.T h).Additive]
include transitionAdditive

end Linear
end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme
attribute [local irreducible] pbcRationalCoefficientEquiv
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

section StageScalars
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u})

end StageScalars

section QbarCoefficients
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

end QbarCoefficients
end AlgebraicGeometry.Scheme
