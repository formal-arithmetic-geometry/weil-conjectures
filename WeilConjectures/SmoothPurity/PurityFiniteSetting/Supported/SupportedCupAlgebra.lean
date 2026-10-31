/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupNativeCoherence
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Native supported cup algebra on either small site

Source: Stacks Project, Tags 0FPL, 0FPM and 03PL.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory AlgebraicGeometry
universe u
namespace WeilConjectures.PurityFiniteSetting

private theorem algebra_add_left (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraAddLeft pro := by
  unfold FunctorialCupAlgebraAddLeft
  intro C D X aX i j hi hj a b r s α α' β
  simp only [functorialCup, ProEtale.cupComposite, MonoidalCategory.tensorHom_def,
    MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

private theorem algebra_add_right (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraAddRight pro := by
  unfold FunctorialCupAlgebraAddRight
  intro C D X aX i j hi hj a b r s α β β'
  simp only [functorialCup, ProEtale.cupComposite, MonoidalCategory.tensorHom_def,
    MonoidalPreadditive.whiskerLeft_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem algebra_smul_left (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraSmulLeft pro := by
  unfold FunctorialCupAlgebraSmulLeft
  intro C D X aX i j hi hj a b r s c α β
  have : MonoidalLinear P.Coefficient (P.FunctorialCupDerived pro X) := by
    cases pro <;> infer_instance
  simp only [functorialCup, ProEtale.cupComposite, MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

private theorem algebra_smul_right (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraSmulRight pro := by
  unfold FunctorialCupAlgebraSmulRight
  intro C D X aX i j hi hj a b r s c α β
  have : MonoidalLinear P.Coefficient (P.FunctorialCupDerived pro X) := by
    cases pro <;> infer_instance
  simp only [functorialCup, ProEtale.cupComposite, MonoidalCategory.tensorHom_def,
    MonoidalLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

/-- Native supported cup algebra on either small site.

Source: Stacks Project, Tags 0FPL, 0FPM and 03PL; supported functoriality proof steps
1--5 and 8.
(blueprint: lem-pur-supported-cup-native-algebra).

Proof: The unit-normalized exchange is an identity on an identity square. On a pasted
square its two composites respect the same epic constant-section map, hence agree.
The signed Tate pullbacks satisfy the corresponding identity and composition laws.
Substituting these equations in normalized exact inverse image proves the first two
fields. The Kummer class is the connecting map of the power sequence followed by its
root coefficient map. Additivity of connecting maps and naturality of the power
sequence give kummer_add and kummer_pullback, including the identity direct-image
unitor used by functorialCupKummer. The tensor bifunctor and coefficient map are
bilinear, giving the four additive and scalar fields. For associativity, expand each
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
theorem supportedCupAlgebra (P : PurityFiniteSetting.{u}) (pro : Bool) :
    P.FunctorialCupAlgebraLaws pro := by
  obtain ⟨hi, hc, hka, hkp, ha, hs, hp⟩ := supportedCupNativeCoherence P pro
  exact {
    identity := hi
    composition := hc
    kummer_add := hka
    kummer_pullback := hkp
    add_left := algebra_add_left P pro
    add_right := algebra_add_right P pro
    smul_left := algebra_smul_left P pro
    smul_right := algebra_smul_right P pro
    associativity := ha
    symmetry := hs
    pullback := hp
  }

end WeilConjectures.PurityFiniteSetting
