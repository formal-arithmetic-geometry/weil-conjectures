/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteBundleSectionAdjointScalar

/-! Transport of the ordinary bundle-section square through the published
pro-etale presentations.

The ordinary equation is the output of finite bundle-section scalar compatibility;
this statement packages the remaining presentation, counit and naturality paste.
(blueprint: lem-pur-finite-diagonal-vector-reduction-presentation-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The ordinary bundle-section scalar equation yields the displayed pro-etale
diagonal vector reduction after expanding the canonical presentations.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity proof Steps 2--4.
Proof: the smooth separated diagonal is regular of codimension `d`; the diagonal
chart normalization identifies its normal cone and augmentation section with the
conormal vector bundle `(π, z)`, and section-scalar base change identifies the
section map of `hcore` with the map `q` transported by `normalSectionMap`. By
vector-bundle purity the zero-section integration adjuncts `a_A : L_A → C_A` and
`a_B : L_B → C_B` are isomorphisms; composing `hcore` with `Q(a_A⁻¹)` on the left and
`a_B⁻¹` on the right gives `Q(a_A⁻¹) ≫ r_d = q ≫ a_B⁻¹`, `r_d = (e.tensorPower d).hom`.
The vector-integration site comparison (with its independence of the annihilating
exponent) identifies the chart factor of `vectorFactor` at each level with `a_R⁻¹`,
so `v_R.hom = c_R.hom ≫ ν_R(a_R⁻¹)` for the specified presentations `c_R`, while
`normalSectionMap = Q(c_A.hom) ≫ δ_{C_A} ≫ ν_B(q) ≫ c_B.inv` and
`proTwistMap d e = δ_{L_A} ≫ ν_B(r_d)` with `δ` the natural site/scalar comparison.
Naturality of `δ` at `a_A⁻¹` and cancelling `c_B.inv ≫ c_B.hom` reduce the goal to the
displayed equation above. `d = 0` and `m = n` are included.
(blueprint: lem-pur-finite-diagonal-vector-reduction-presentation-transport). -/
theorem finiteDiagonalPresentationTransport
    (e : CoefficientLineComparison (quotient P m hm hmn)
      P.diagonalExponent (P.finiteReductionSetting m hm).diagonalExponent
      P.diagonalExponent_annihilates
      (P.finiteReductionSetting m hm).diagonalExponent_annihilates X)
    : letI := P.noetherian (f ≫ aY)
      letI := (chartDiagonalNormalBundle d f).1
      (hcore :
      (ordinaryScalar (quotient P m hm hmn) X).map
          (Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
            P.diagonalExponent (by
              dsimp only [PurityFiniteSetting.diagonalExponent]
              exact pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
            P.diagonalExponent_annihilates X
            (P.diagonalExponent_isUnit (f ≫ aY)) d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) ≫
        DncCoefficientTransport.sectionMap (quotient P m hm hmn)
          (VectorBundleZeroSection.π X d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1))
          (VectorBundleZeroSection.zero X d
            (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) =
      (e.tensorPower d).hom ≫
        Etale.FiniteRingSectionDeformation.bundleSectionAdjoint
          (P.finiteReductionSetting m hm).diagonalExponent (by
            dsimp only [PurityFiniteSetting.diagonalExponent]
            exact pow_pos P.coefficients.prime.out.pos m)
          (P.finiteReductionSetting m hm).Coefficient
          (P.finiteReductionSetting m hm).diagonalExponent_annihilates X
          ((P.finiteReductionSetting m hm).diagonalExponent_isUnit (f ≫ aY)) d
          (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)) →
      (proScalar (quotient P m hm hmn) X).map (vectorFactor P d f aY).hom ≫
        proTwistMap d e =
      normalSectionMap P m hm hmn d f aY ≫
        (vectorFactor (P.finiteReductionSetting m hm) d f aY).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
