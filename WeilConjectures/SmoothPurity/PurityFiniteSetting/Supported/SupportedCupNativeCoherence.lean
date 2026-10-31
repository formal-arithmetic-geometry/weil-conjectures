/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

/-! # Native supported cup algebra on either small site

Source: Stacks Project, Tags 0FPL, 0FPM and 03PL.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurityFiniteSetting

/-- Coherence and Kummer laws of native supported cups.

Source: Stacks Project, Tags 0FPL, 0FPM and 03PL; supported functoriality proof steps
1--5 and 8.
(blueprint: lem-pur-supported-cup-native-coherence).

Proof: The unit-normalized exchange is an identity on an identity square. On a pasted
square its two composites respect the same epic constant-section map, hence agree.
The signed Tate pullbacks satisfy the corresponding identity and composition laws.
Substituting these equations in normalized exact inverse image proves the first two
fields. The Kummer class is the connecting map of the power sequence followed by its
root coefficient map. Additivity of connecting maps and naturality of the power
sequence give kummer_add and kummer_pullback, including the identity direct-image
unitor used by functorialCupKummer. For associativity, expand each
cup as inverse supported coefficient multiplication, shifted tensor of the two
arrows, then Tate multiplication. Naturality of the associator, associativity of
closed-source multiplication and Tate multiplication, and the cocycle equation
for the sign (-1)^(ba) identify both composites. Reindexing accounts for their
parenthesized integer sums. The symmetry equation uses the same expansion and
the braiding: the two coefficient multiplications are symmetric and the shift
braiding contributes (-1)^(ab). Exact tensor inverse image respects all these
constraints, so its monoidal square cancels the normalized source and twist
exchanges and proves the cup pullback equation. These computations are valid
for negative degrees, zero coefficients, empty supports and degree-zero twists;
no geometric stalk conservativity on the pro-etale site is used. -/
theorem supportedCupNativeCoherence (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraIdentity pro ∧ P.FunctorialCupAlgebraComposition pro ∧
      P.FunctorialCupAlgebraKummerAdd pro ∧ P.FunctorialCupAlgebraKummerPullback pro ∧
      P.FunctorialCupAlgebraAssociativity pro ∧ P.FunctorialCupAlgebraSymmetry pro ∧
      P.FunctorialCupAlgebraPullback pro := by
  sorry

end WeilConjectures.PurityFiniteSetting
