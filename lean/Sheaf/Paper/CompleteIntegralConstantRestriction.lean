/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T9
-/
module

public import Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison

/-! # Complete integral objects in constant-coefficient coordinates

Source: Stacks 099I, 099L, 099N; the scalar-coordinate part of
lem-pur-compact-support-limit-equation-realization, Steps 1 and 9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompactSupportLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Scalar restriction of a complete integral object has an invertible constant
completion unit, and detects equality of maps between such integral objects.
Source: Stacks 099I, 099L, 099N; parent proof Steps 1 and 9
(blueprint: lem-pur-complete-integral-constant-restriction).

Proof: the first component of finiteTorConstructibleIntegral gives membership in
sfIntegralConstructible, hence intrinsic derived completeness over completed scalars.
The flat constant-to-completed coefficient comparison identifies the principal
uniformizer ideals and all their positive quotients. Restriction therefore carries
this object into the complete constant-coefficient subcategory. Transport along the
exact small-site module equivalence in ordinaryH preserves the quotient tower, total
limit and its actual augmentation. The completion-unit criterion on this site makes
the displayed unit invertible. For the second assertion apply the fully faithful
constant/completed equivalence to the two complete objects, then the faithful exact
small-site equivalence. The resulting map on Hom is precisely H.map, so it is
injective. No claim of faithfulness on the whole ambient derived category is used.
The zero object and empty site satisfy the same argument; the Tor interval and
constructibility are used only to extract completeness. -/
theorem completeIntegralConstantRestriction (W : Scheme.{u})
    (M : IntegralSystemRealization.Integral l E W)
    (hM : finiteTorConstructibleIntegral l E W M) :
    IsIso (((sfCbcSite W).unit _
      (sfCbcModelIdeal (GeneratorReduction.constantDatum l E))).app
        ((GeneratorReduction.H l E W).obj M)) ∧
    ∀ (N : IntegralSystemRealization.Integral l E W),
      finiteTorConstructibleIntegral l E W N →
        Function.Injective ((GeneratorReduction.H l E W).map (X := M) (Y := N)) := by
  sorry

end WeilConjectures.CompactSupportLimit
