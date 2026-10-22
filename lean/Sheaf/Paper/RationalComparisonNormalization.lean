/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonDatum

/-! # Normalized equations for the concrete rational comparison

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent
attribute [local semireducible] FieldOf integerRing
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)


attribute [local instance] rationalStructures

/-- The eight scalar normalization equations for the explicit rational datum.
Source: blueprint order 1826, conditional scalar comparison construction
(blueprint: lem-sf-rational-comparison-normalization).

Proof: the inverse tensor and unit maps of the composite core are B applied to the
integral inverse comparison followed by the normalized scalar tensor and unit maps.
Compose the integral symmetry square with normalized scalar symmetry. Expanding phi
and cancelling the inverse scalar comparisons gives its prescribed component formula.
On bounded finite-projective models, the model equations identify the perfect scalar
identity and tower maps with the exact field identity and tower maps; naturality
transports the equalities to every perfect object. The two scalar tower units and
four-ring equation, combined with integral clauses 14--15, prove phi identity and
tower. Finally combine integral clauses 16--17 with the normalized scalar tensor and
coefficient-unit tower squares to obtain the last two equations.
-/
theorem rationalDatum_normalization :
    RationalData.condition10 C A (rationalDatum A hA) ∧
    RationalData.condition11 C A (rationalDatum A hA) ∧
    RationalData.condition12 C A (rationalDatum A hA) ∧
    RationalData.condition23 C A (rationalDatum A hA) ∧
    RationalData.condition24 C A (rationalDatum A hA) ∧
    RationalData.condition25 C A (rationalDatum A hA) ∧
    RationalData.condition30 C A (rationalDatum A hA) ∧
    RationalData.condition31 C A (rationalDatum A hA) := by
  sorry

end WeilConjectures.TensorComparisonDescent
