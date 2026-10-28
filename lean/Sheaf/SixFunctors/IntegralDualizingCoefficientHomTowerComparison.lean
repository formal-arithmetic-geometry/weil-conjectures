/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T9
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.Paper.CoefficientDuality

/-! # The resolved coefficient Hom tower comparison

Source: current blueprint prop-coef-integral-dualizing, final displayed comparison;
Stacks 0941 and 08J9.

(blueprint: lem-coef-integral-dualizing-coefficient-hom-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The resolved comparison map from the constant-coefficient Hom tower to the
coefficient derived dual.  Its construction uses one K-flat representative and
one simultaneous K-injective representative of the quotient tower; the Roos
calculation and completeness identify the resulting map with the derived dual.
The assertion records the natural transformation and the componentwise
isomorphism property separately, so the enclosing functor-isomorphism theorem
only performs the categorical assembly.

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph,
three displayed mapping-complex comparisons; Stacks 0941 and 08J9.
(blueprint: lem-coef-integral-dualizing-coefficient-hom-tower-comparison).
-/
theorem integralDualizing_coefficient_hom_tower_comparison :
    ∃ α : integralDualizingCoefficientHomTower l E ⋙
        CoefTower.totalLimit (integralDualizingCoefficients l E) ⟶
      coefficientDerivedDual (integralDualizingCoefficients l E),
      ∀ C : DerivedCategory (ModuleCat.{u + 1}
        (integralDualizingCoefficients l E)),
        IsIso (α.app (op C)) := by
  sorry

end WeilConjectures
