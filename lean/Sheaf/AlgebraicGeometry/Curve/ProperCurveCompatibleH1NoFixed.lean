/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
public import Sheaf.AlgebraicGeometry.Curve.H1DualTateModule
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction
import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
import WeilConjectures.GroupTheory.TateModule

/-! # No fixed compatible first cohomology class on a proper curve

Source: Weil conjectures blueprint, main-20261015, sec-purity-real-sheaves,
sk-p-real-rankone, equation (4.4)
(blueprint: lem-wf-proper-curve-compatible-h1-no-fixed).

The ordinary inverse limit is the existing `curveH1CoefficientSystem` with the actual
coefficient reductions. Its groups use `Sheaf.H`, the Ext model of the recorded
`Etale.cohomology`. Frobenius is the recorded geometric Galois automorphism, followed on
cohomology by the canonical constant-sheaf identification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every geometric-Frobenius-fixed compatible integral H¹ class on a smooth projective
geometrically connected curve over a finite field is zero.
Source: blueprint main-20261015, sk-p-real-rankone, equation (4.4)
(blueprint: lem-wf-proper-curve-compatible-h1-no-fixed).

Proof, following the three DAG steps:
1. Choose the geometric Jacobian and its canonical semilinear Galois action using
`lem-wf-geometric-jacobian-galois-action`. Apply `lem-wf-curve-h1-dual-tate-module` to
identify the ordinary inverse limit with Hom over ℤ_ℓ from T_ℓ J to ℤ_ℓ, equivariantly.
The dual action is contragredient. Since the geometric operator of
`def-weil-frobenius-detailed` is induced by γ_Q = σ_Q⁻¹, a fixed class gives a functional f
with f(σ_Q t) = f(t), hence f((σ_Q - 1)t) = 0.
2. By `lem-wf-finite-field-tate-no-fixed`, σ_Q - 1 is invertible on V_ℓ J. The definitions
`def-wf-abelian-tate-module` and `def-tate-module-abelian-group` identify this space with
T_ℓ J[1/ℓ]. For t in T_ℓ J choose a preimage ℓ⁻ᵇu. The equality criterion for fractions
supplies d with ℓᵈ((σ_Q - 1)u - ℓᵇt) = 0. Applying f gives ℓ^(b+d) f(t) = 0. This does not
require injectivity of the integral module into its localization.
3. The compatible-residue ring ℤ_ℓ has no ℓ-power torsion: if ℓᵃc = 0, the residue at
level n+a is divisible by ℓⁿ, so its reduction c_n is zero at every positive level n.
Apply this to f(t), deduce f = 0, and use injectivity of the comparison in step 1.
Level n = 0 is the zero-coefficient group and does not change the ordinary inverse limit. -/
theorem properCurve_compatibleH1_fixed_eq_zero
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (C₀ : Over (Spec (.of D.k₀)))
    [SmoothOfRelativeDimension 1 C₀.hom] [IsProjective C₀.hom]
    [GeometricallyConnected C₀.hom]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ D.q)
    (x : ↥(limit (curveH1CoefficientSystem (D.geometricFiber C₀).left ℓ)))
    (hfix : ∀ n : ℕ,
      Sheaf.H.map
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (D.geometricFrobenius C₀).hom).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))).hom) 1
        (Etale.cohomologyMap (D.geometricFrobenius C₀).hom
          ((D.geometricFiber C₀).left.constantZMod (ℓ ^ n)) 1
          (limit.π (curveH1CoefficientSystem (D.geometricFiber C₀).left ℓ) (.op n) x)) =
        limit.π (curveH1CoefficientSystem (D.geometricFiber C₀).left ℓ) (.op n) x) :
    x = 0 := by
  sorry

end AlgebraicGeometry
