/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AlgebraicallyClosedCoefficients.AlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Scalar.ScalarExtensionExactIntrinsic
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemVerdier
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Colimit.Module
public import WeilConjectures.SmoothPurity.SfAlgebraicallyClosedCoefficients.SfCoefficientStageCore

import WeilConjectures.CategoryTheory.StageSystem.Shift

/-! # Intrinsic algebraically closed coefficients without idempotent completion

Source: blueprint `sec-smooth-purity/sk-def-sf-operations`, order 1462;
current main snapshot `sec-proetale-coefficients/sk-def-sf-operations`, order 1821
(blueprint: def-weil-algebraically-closed-coefficients).
Objects are actual pairs and Hom is the directed colimit of the stated abelian groups.
Finite stages use the repaired intrinsic integral constructibility predicate.

The similarly named legacy theorems quantify over `AlgebraicallyClosedCoefficients.Stage`,
which uses `rationalConstructibleCategory` and the withdrawn integral predicate.
Here the eleven formerly ambiguous signatures bind every source parameter explicitly
and qualify their intrinsic stage, pair, transition and Hom data. They concern
`sfRationalConstructibleCategory` on `sfIntegralConstructibleCategory`; no identification
with the legacy stages is assumed. Existing generic pair/cone/Verdier constructions
and the shared coefficient transport are reused.
The legacy coefficient-size transports are reused without identifying the old and new stages.
The existing upstream pair category supplies its quotient, identities and composition;
its Hom groups are canonically the displayed abelian-group colimits.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe d u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace WeilConjectures
namespace SfAlgebraicallyClosedCoefficients

attribute [-instance] StageSystem.PairCategory.hasShift StageSystem.ι_commShift
  StageSystem.transIso_commShift

section PairShiftNormalization

attribute [local instance] StageSystem.PairCategory.hasShift StageSystem.ι_commShift
  StageSystem.transIso_commShift

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j k : I) (h : i ≤ j) (k : j ≤ k), NatTrans.CommShift (S.assoc h k).hom ℤ]

variable [∀ i, Preadditive (C i)]
  [∀ i (n : ℤ), (shiftFunctor (C i) n).Additive] [Preadditive S.PairCategory]

end PairShiftNormalization

attribute [local irreducible] ScalarLocalization.category sfRationalTriangulationDatum

open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (Y : AlgebraicGeometry.Scheme.{u})

section
attribute [local irreducible] stageCategory transition associator unitor
  stagePreadditive stageShift stagePretriangulated

end

attribute [local irreducible] stageCategory

attribute [local instance] stageAssociator_commShift

variable {D l hl Ω Y}

attribute [instance] zero_exists

end SfAlgebraicallyClosedCoefficients

end WeilConjectures
