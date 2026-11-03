/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted

/-! # Current integral scalar and Tate-line comparison

Source: current blueprint, integral-adjunction-bijection, Purity paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction
open IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual integral signed line in degree zero, with the purity shift.
Source: coefficient twists and integral-adjunction-bijection, Purity
(blueprint: lem-sp-current-integral-twist-tensor-reduction). -/
def shiftedIntegralLine (T : Scheme.{u}) (d : ℕ) : Integral l E T :=
  letI := spectralNorm.normedField (Padic l) E
  letI : MonObj (spIntegralCondensed l E) :=
    Profinite.continuousMapRingObjOfUniverseMonObj (Padic.coefficientExtensionIntegers l E)
  letI : MonObj (condensedRingObj (spIntegralCondensed l E) T) :=
    (upperStarFromPoint T).monObjObj (spIntegralCondensed l E)
  ((DerivedCategory.singleFunctor _ 0).obj
    (coefficientSignedTwist T _ (coefficientIntegralTwistOne l E T) (d : ℤ)))⟦2 * (d : ℤ)⟧

/-- Reduction of tensor and shift is tensor with the reduction of the shifted line.
The isomorphism is in the derived category of entire strict quotient systems.

Source: current blueprint, integral-adjunction-bijection, Purity, compatible reduction
sentence; direct-image (3), scalar tensor comparison.
(blueprint: lem-sp-current-integral-twist-tensor-reduction).

Proof: choose flat-term K-flat resolutions of the input and of the signed Tate
line placed in degree zero. No flatness of that line on an arbitrary T is assumed.
The relative scalar-extension tensor associator gives the
comparison at every quotient. On elementary tensors it sends the reduction of
x tensor t to the tensor of the reductions of x and t; balancing gives the inverse.
Both maps commute with the quotient-induced transitions, hence define maps of the
whole strict systems before localization. The section/internal equivalence retains
these maps and scalar actions. The universal derived-functor comparisons therefore
give a natural isomorphism for the chosen current reduction. Apply the cochain
shift/tensor comparison with its standard signs to move the even shift onto the
line. The zero power uses the scalar unitor and rank-zero inputs give the zero map.
No purity isomorphism or exceptional adjunction is used. -/
theorem integral_twist_tensor_reduction
    (s : Presentation l E) (T : Scheme.{u}) (d : ℕ) :
    Nonempty
      (coefficientIntegralTwistFunctor l E T (d : ℤ) ⋙
          shiftFunctor _ (2 * (d : ℤ)) ⋙ derivedReduction l E s T ≅
        derivedReduction l E s T ⋙
          Prod.sectL (SpTowerShriek.D l E T)
            ((derivedReduction l E s T).obj (shiftedIntegralLine l E T d)) ⋙
          SpTowerShriek.tensor l E s.base T) := by
  sorry

end AlgebraicGeometry.ProEtale.SpCondensedIntegralAdjunction
