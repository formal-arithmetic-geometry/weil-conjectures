/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackReductionData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.IntegralLineReductionDefinitions
public import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerChartData
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculusSupplement
import WeilConjectures.AlgebraicGeometry.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.TateTwistLocallyFree
import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SemilinearSystemIsoAssembly
import WeilConjectures.Algebra.Homology.DerivedTensorAdditiveConstraints
import WeilConjectures.AlgebraicGeometry.IntegralLinePowerComparisons
import WeilConjectures.CategoryTheory.SystemRingedSequenceSite
import WeilConjectures.AlgebraicGeometry.EllCoefficientFiber

/-! # Tensor and shift comparison for the ordered Tate line

Source: latest blueprint, sec-smooth-purity, sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-bijection.proof.md, Purity paragraph
(blueprint: lem-route-integral-adjunction-ordered-line-tensor-shift).

The comparison is between endofunctors of the unbounded derived category of strict
coefficient systems. Its right tensor factors are the recorded reduced integral line
and the recorded ordered product, respectively.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpIntegralAdjunction

/-- Tensoring with the reduced integral degree-d Tate line followed by shift 2d is
naturally isomorphic to tensoring with the ordered product of d degree-one lines,
each shifted by two. Source: latest blueprint, integral-adjunction-bijection proof,
Purity paragraph (blueprint: lem-route-integral-adjunction-ordered-line-tensor-shift).

Proof:
1. Use def-sp-reduction-tower-data and lem-sp-ell-coefficient-fiber to identify the
ordinary first-power reduction B_n tensor_R P with its discrete-coefficient quotient
Q_n. Both are P/ell^(n+1)P; the comparison sends 1 tensor x to 1 tensor x and the
transition sends t tensor x to tau_n(t) tensor x (def-pur-twist-sheaves and
 def-sp-ell-twist-quotient-data).
2. The compatible-root cover of det-def-sp-tate-twist-locally-free trivializes every
positive integral power, including the unit at zero. These lines are flat and their
singletons are K-flat by lem-pur-derived-tensor-additive-constraints. The universal
K-flat comparison of def-sp-reduction-tower-data, followed by the exact realization
of def-sp-twisted-pullback-reduction-data, identifies the reduced derived line with
the degree-zero embedding of its ordinary strict reduction A_d.
3. Form ordinary systems H_0 equal to the coefficient unit and H_(r+1)=H_r tensor S,
where S=w.tower 1. At level n, compose the positive-power comparison of
lem-pur-integral-line-power-comparisons, the tensor powers of the first-power
quotient comparison, and the inverse powers of w.level n 1. Insert the initial unit
by the ordinary unitor. This gives ordinary isomorphisms (A_d)_n to (H_d)_n.
4. Check their transition squares on local pure tensors. At zero use multiplication
and coefficient reduction; at one use the normalized c_1 generator formula. For the
successor, the positive recursion in def-pur-signed-line-scalar-normalization-data
and w.normalized gives the tensor of the preceding square and the degree-one
square. The initial unit is preserved since tau_n(1)=1. Generators determine the
sheaf maps. Compose adjacent squares to obtain all-index compatibility.
5. Apply lem-coef-system-iso-assembly only to these ordinary abelian systems and
ordinary level isomorphisms. Then apply the degree-zero embedding and Step 2 to
obtain an actual isomorphism L_d to H_d[0] in the derived category of systems.
6. By lem-pur-system-ringed-sequence-site these systems are modules on the ringed
sequence site. Levelwise exactness from det-sp-coefficient-towers-abelian and the
local rank-one property show S is flat. Apply the flat-singleton comparisons of
lem-pur-derived-tensor-additive-constraints recursively. Its fully faithful
restriction clause identifies its site tensor with the fixed tensor of
 def-sp-tower-shriek-data, def-coef-semilinear-derived-calculus and
 def-coef-ringed-tensor-hom-model through their K-flat representative comparisons.
Thus H_r[0] represents the unshifted ordered derived tensor word.
7. Induct on r using def-sp-tower-gamma-data. At zero both units agree. At the
successor apply the natural tensor-shift isomorphism t_(2r,2) and the shifted
flat-singleton comparison. Since 2r+2=2(r+1), this identifies O_r with H_r[0][2r],
with precisely the recorded left parentheses and no permutation.
8. Shift Step 5 by 2d and compose with the inverse of Step 7 to obtain
lambda_d:L_d[2d] to O_d. For arbitrary derived M use the inverse of t_(0,2d),
with the zero-shift comparison, followed by identity tensor lambda_d. The tensor
shift constraint is natural on all derived objects and bifunctoriality proves
naturality for every derived morphism. No componentwise lifting is used. -/
theorem integralAdjunctionOrderedLineTensorShift
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (hX : ∀ x : X, Invertible (l : X.residueField x))
    (b : SpTowerShriek.Base l E) (q : SpTowerCalculus.Coordinates l E b)
    (R : SpReductionTower l E X (q.abelian X))
    (w : SpChartAdmissibility.Twists l E X) (d : ℕ) :
    Nonempty
      ((Prod.sectL (SpTowerShriek.D l E X)
          (SpTwistedPullback.line l E b X (q.abelian X) R (d : ℤ)) ⋙
        SpTowerShriek.tensor l E b X ⋙ shiftFunctor _ (2 * (d : ℤ))) ≅
        (Prod.sectL (SpTowerShriek.D l E X) (SpTowerGamma.orderedLine l E b X w d) ⋙
          SpTowerShriek.tensor l E b X)) := by
  sorry

end AlgebraicGeometry.ProEtale.SpIntegralAdjunction
