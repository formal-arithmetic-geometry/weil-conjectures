module

public import Sheaf.SecSmoothPurity.NestedAffineFormulaData

/-! # Normalization and finite-Tor inputs for affine integration

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, proof (1).
(blueprint: lem-sp-nested-affine-normalized-inputs).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.NestedAffine

/-- Normalization and finite-Tor inputs for affine integration.

Source: composition-factors proof (1).
(blueprint: lem-sp-nested-affine-normalized-inputs).

Proof:
1. Apply projection-purity-agreement to the affine projection at every ordinary
   constructible finite-Tor input, using the canonical finite-site comparison.
   Its tensor and exceptional comparison squares preserve the published counits,
   so full faithfulness reflects the equation back to the ordinary category.
2. Expand the smooth purity map: it is tensor of the pullback identity with the
   inverse diagonal orientation, followed by smoothPurityEtaleTheta. At the
   coefficient unit dualizingTensor_unit cancels the coefficient-unit constraints.
   This gives orientation = gammaUnit, with the same ordered Tate source.
3. The coefficient unit has Tor interval [0,0]. Exceptional preservation gives
   the finite-Tor assertion for the dualizing object and for every exceptional
   input. Pullback and tensor with the locally free shifted Tate line preserve
   finite Tor amplitude and bounded constructibility, giving OrdinarySource.
4. At rank zero the affine adjunction is the identity adjunction. Its transpose
   is the identity with precisely the exceptional-identity, pullback-identity
   and right-unit constraints in zeroSource. Evaluating at the coefficient unit
   gives the last equation. All these equations include the empty scheme.
-/
theorem nested_affine_normalized_inputs (P : PurityFiniteSetting.{u}) :
    NormalizedInputs P := by sorry

end WeilConjectures.PurityFiniteSetting.NestedAffine
