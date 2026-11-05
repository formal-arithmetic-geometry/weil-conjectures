/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExact
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.LinearAlgebra.Dimension.Free

import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import WeilConjectures.CategoryTheory.StageSystem.Shift
import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionAssociatorShifts
import Mathlib.Algebra.Group.Ext

/-! # Algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe d u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures

section
attribute [local irreducible] rationalTriangulationDatum rationalConstructibleScalarComp

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
  (Y : AlgebraicGeometry.Scheme.{u})

end

section
universe w₁ v₁ u₁
variable {I : Type w₁} [Preorder I] {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]
end

section
universe w₁ v₁ u₁
variable {I : Type w₁} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u₁} [∀ i, Category.{v₁} (C i)] (S : StageSystem C)

end

section
variable {C D : Type*} [Category* C] [Category* D]
end

section
variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

end

section
variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (Y : AlgebraicGeometry.Scheme.{u})
end

namespace AlgebraicallyClosedCoefficients

attribute [local irreducible] rationalTriangulationDatum rationalScalarExtension
  rationalConstructibleScalarComp rationalConstructibleScalarUnit
  Padic.finiteCoefficientBase Padic.finiteCoefficientCompositum

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

attribute [local irreducible] stageSystem

attribute [local irreducible] stageCategory stagePreadditive stageShift stagePretriangulated

variable {D l hl Ω Y}

attribute [instance] zero_exists

end AlgebraicallyClosedCoefficients

end WeilConjectures
