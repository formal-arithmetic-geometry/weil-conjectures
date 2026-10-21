/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.Paper.IntegralTwistBaseChangeDefinitions
import Sheaf.Paper.SignedLineScalarPullbackSquare

/-! Geometric signed compatibility of integral twists.
Source: main-20261015 blueprint, final sentence of the twist-preservation proof
(blueprint: lem-weil-integral-twist-scheme-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Geometric signed inverse-image compatibility for integral twists.
Source: main-20261015, `prop-weil-twist-preserves.proof.md`, final sentence;
Stacks, Modules on Sites, 03EL and 0GMX.
(blueprint: lem-weil-integral-twist-scheme-compatibility).

Proof:
1. Apply `pur_integral_twist_line_inverse_image` to obtain the coefficient and
root-limit isomorphisms and the normalized first-line maps with their two squares.
Transpose the first-line maps under the additive inverse-image adjunction. Their
semilinearity makes these actual module maps into module direct images. Transpose
again under the module pullback adjunction to get linear first-line comparisons.
2. Extension along an isomorphism of coefficient sheaves is restriction along its
inverse: the maps on tensors are s tensor x to alpha inverse(s) times x and x to
1 tensor x. Thus the underlying module pullback is the actual additive inverse
image. Uniqueness of left adjoints identifies these comparisons with the chosen
module pullbacks and preserves their adjunction-unit sections. In particular the
linear first-line comparisons are isomorphisms because their additive maps are.
3. Identify coefficientTwistPower with scalarTensorPower by two-step induction,
and coefficientTwistLine with signedLinePower by cases on the integer. Transport
twistLineScalarIso along the ordinary-scalar object equality. Its pure-tensor
formula, and the normalization of twistScalarMaps, identify its degree zero with
the scalar unit, its positive recursion with the tensor comparison, and its
negative map with the dual scalar comparison followed by inverse precomposition.
For the negative equality, precompose evaluation with the invertible positive
comparison; equality on pure scalar tensors determines the internal-Hom map.
4. The rank-one theorem gives trivializing covers for all four first lines.
The coefficient square gives the square of adjunct structural ring maps.
On a pure tensor s tensor x, the linearized first-line square is the given
additive square multiplied by the image of s, using semilinearity. Apply
`existsUnique_signedLineScalarPullbackSquare` to these data.
5. Forget its signed module isomorphisms and compose with the inverse-image
comparisons of step 2. The adjunction-unit formulas identify their adjuncts
with the module unit followed by the signed maps. Consequently the generic
zero, degree-one, positive recursion and dual-evaluation equations are exactly
the displayed inverse-comparison predicate. Module linearity gives its scalar
clause. The root clause follows from the original degree-one comparison.
6. For the final square apply injectivity of the additive adjunction's Hom
equivalence. At V and x, specialize the generic signed scalar square to 1 tensor x.
Naturality of both adjunction units and the scalar pure-tensor formulas turn its
two sides into the adjuncts of the two requested composites. Thus they agree as
sheaf morphisms, in every signed degree. The coefficient square is retained
unchanged from step 1. No flatness is used; the line and all its dual powers are
trivial on the stated covers.
-/
theorem integral_twist_base_change_scheme
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (S : Scheme.{u})
    [∀ x : S, Invertible (l : S.residueField x)] :
    ∀ (X : Scheme.{u}) (h : X ⟶ S)
        [∀ x : X, Invertible (l : X.residueField x)],
      ∃ (αE : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l E S) ⟶
            completedIntegralCommRingSheafUnrestricted l E X)
        (αF : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj
          (completedIntegralCommRingSheafUnrestricted l F S) ⟶
            completedIntegralCommRingSheafUnrestricted l F X)
        (τ : (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (purTwistZlOne S l) ⟶ purTwistZlOne X l)
        (ρE : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l E S m) ≅ integralTwistUnderlying l E X m)
        (ρF : ∀ m : ℤ, (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).obj
          (integralTwistUnderlying l F S m) ≅ integralTwistUnderlying l F X m),
        (IsIso αE ∧ IsPurIntegralCoefficientComparison h l E αE) ∧
        (IsIso αF ∧ IsPurIntegralCoefficientComparison h l F αF) ∧
        (IsIso τ ∧ IsPurRootLimitComparison h l τ) ∧
        IsIntegralTwistInverseComparison l E h αE τ ρE ∧
        IsIntegralTwistInverseComparison l F h αF τ ρF ∧
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
            (integralCompletedScalarMap l E F ι S) ≫ αF =
          αE ≫ integralCompletedScalarMap l E F ι X ∧
        ∀ m : ℤ,
          (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}).map
              (integralTwistScalarUnderlying l E S F ι m) ≫ (ρF m).hom =
            (ρE m).hom ≫ integralTwistScalarUnderlying l E X F ι m := by
  sorry

end WeilConjectures
