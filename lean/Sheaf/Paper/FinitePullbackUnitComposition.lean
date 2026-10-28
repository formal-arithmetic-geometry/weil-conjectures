/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.Paper.CoefficientPullbackUnitCoordinates

/-! # Composition of finite coefficient multiplication

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
step 3 (blueprint: lem-zl-finite-pullback-unit-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.ConstantGeometricStalkUnit

/-- The actual finite compositor preserves regular coefficient multiplication.
Source: current blueprint, sec-zeta-weil/sk-thm-intfactors,
`prop-every-iterate-trace.proof.md`, constant-sheaf clause, reviewed expansion step 3.
(blueprint: lem-zl-finite-pullback-unit-composition).

Proof: transpose the regular multiplication maps along the module adjunctions.
Each is the section one. The constant coefficient direct-image ring maps respect
composition by `proEtaleCoefficientInverseImageMap_comp`. The unit-normalized
changes of pullback presentation preserve these transposes. The canonical tensor
compositor sends an iterated pure tensor to its associated tensor, so both paths
multiply its coefficients in the same order. The regular sheaf in degree zero is
K-flat, and the single-complex comparison is natural, giving the displayed equation
in the derived category. This also applies to identity maps, empty schemes and m=0. -/
theorem finiteUnit_composition
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (m : ℕ) :
    (finiteCanonicalPullbackComposition l E f g m).hom.app
        (finiteConstantCoefficientObject l E Z m) ≫
      (finiteDerivedPullback l E m f).map (finiteUnit l E g m).hom ≫
        (finiteUnit l E f m).hom = (finiteUnit l E (f ≫ g) m).hom := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
