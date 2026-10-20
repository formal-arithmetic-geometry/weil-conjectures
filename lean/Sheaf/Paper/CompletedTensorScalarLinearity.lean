/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfIntegralConstructibleLinear

/-! # Scalar linearity of the completed tensor

Source: Stacks 06YS and 0941; completed tensor-Hom transpose, proof step 3
(blueprint: lem-coef-completed-tensor-scalar-linearity).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- Completed tensor is linear in its first morphism with the second fixed.
Source: Stacks 06YS and 0941; parent transpose proof step 3.
Proof: on flat-term K-flat representatives, scalar multiplication acts by the
constant completed section in each degree. The balanced total tensor sends
(c f) tensor g to c times (f tensor g), componentwise, with unchanged signs.
Every quotient and tower transition commutes with the constant section.
The Roos maps and derived localization preserve this equality. Conjugating by
the normalized descent comparison gives the equality for all derived arrows.
Restriction to the constructible full subcategory changes no morphism or scalar.
Zero objects, zero scalars and arbitrary torsion inputs require no cancellation.
(blueprint: lem-coef-completed-tensor-scalar-linearity). -/
theorem completedTensor_map_smul_left
    (M M' N N' : sfIntegralConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N')
    (c : Padic.coefficientExtensionIntegers l E) :
    (constructibleIntegralTensor l E W).map (Prod.mkHom (c • f) g) =
      c • (constructibleIntegralTensor l E W).map (Prod.mkHom f g) := by
  sorry

end WeilConjectures
