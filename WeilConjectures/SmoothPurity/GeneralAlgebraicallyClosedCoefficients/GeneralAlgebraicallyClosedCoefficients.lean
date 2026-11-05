/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Pi.Basic
public import WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.IntrinsicAssociatorShiftSquare

/-! # Common-stage coefficients over arbitrary schemes

Source: blueprint sec-smooth-purity/sk-def-sf-operations, order 1462;
main-20261015 sec-proetale-coefficients/sk-def-sf-operations, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).

The datum-free intrinsic construction reuses the finite-field interface and its
legacy coefficient transports. Only preservation proofs mention p; choosing zero
there imposes no characteristic on Y. Tensor normalization identifies the resulting
transitions and comparisons with every finite-field specialization. Objects remain
literal pairs, with directed-colimit Hom groups and no Karoubi completion.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] ScalarLocalization.category

attribute [local irreducible] sfRationalConstructibleLocalization
  sfRationalTriangulationDatum sfRationalScalarExtension
  sfRationalScalarComp sfRationalScalarUnit sfIntegralScalarComp sfIntegralScalarUnit
  sfIntegralOrdinaryComparison

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

section PairShiftNormalization

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j k : I) (h : i ≤ j) (k : j ≤ k), NatTrans.CommShift (S.assoc h k).hom ℤ]

variable [∀ i, Preadditive (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [Preadditive S.PairCategory]

end PairShiftNormalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

attribute [local instance] stageAssociator_commShift

attribute [local irreducible] stageCategory transition scalarAssociator associator

variable {l Ω Y}

attribute [local irreducible] unitor

section
attribute [local irreducible] homAddCommGroup

end

attribute [instance] zero_exists

end GeneralAlgebraicallyClosedCoefficients

namespace GeneralAlgebraicallyClosedCoefficients

attribute [local irreducible] homAddCommGroup
  SfAlgebraicallyClosedCoefficients.homAddCommGroup

attribute [local irreducible] ScalarLocalization.composition
  sfRationalScalarExtension sfRationalTriangulationDatum sfRationalConstructibleLocalization

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

attribute [local irreducible] specialization pairCategory
  SfAlgebraicallyClosedCoefficients.pairCategory preadditive
  SfAlgebraicallyClosedCoefficients.preadditive

end GeneralAlgebraicallyClosedCoefficients
end WeilConjectures
