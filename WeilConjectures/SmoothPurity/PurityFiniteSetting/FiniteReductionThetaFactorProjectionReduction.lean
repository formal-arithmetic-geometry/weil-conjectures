/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteReductionThetaFactorSourceCtf

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
section Morphism
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [IsSeparated (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [IsSeparated (Y ↘ Spec (.of P.field.k))]
variable (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The reduced original projection/counit composite equals the projection/counit
composite with the reduced pullback and dualizing-unit map.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 3--4
(blueprint: lem-pur-finite-reduction-theta-factor-projection-reduction).

Proof: put C = f_A^* K tensor omega_A and W = Q_X omega_A. Apply the
projection reduction square det-prop-sf-pf-reduction to (omega_A,K) and
invert both projection comparisons on the finite-Tor domain. The symmetric
monoidal scalar tensorator commutes with symmetry and the unitors. Thus the
reduced counit composite is the B-projection composite with evaluation
v = q_omega.inv followed by Q_Y(epsilon_A,1) and the scalar unit. The
exceptional mate identity at the unit and counit naturality give
v = F_B(w) followed by epsilon_B,1. Naturality of the inverse projection in
w and naturality of tensor symmetry move w to the tensor source. The resulting
source arrow is precisely finiteReductionTensorOmegaComparison. Expand the
specified theta_B transpose to obtain the right side. The intrinsic and site
realization comparison units cancel by their triangle identities. This step
contains no exceptional coefficient comparison at K and asserts no equality of
the original theta arrows.
-/
theorem finiteReduction_thetaFactor_projection_reduction (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K)
    (J : Etale.DerivedCategoryModule P.Coefficient Y)
    (e : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj J ≅
        (Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K)
    (J' : Etale.DerivedCategoryModule (P.finiteReductionSetting m hm).Coefficient Y)
    (e' : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) Y).mapDerivedCategory.obj
        J' ≅
          (Scheme.sfIntrinsicDerivedEquivalence Y (P.finiteReductionSetting m hm).Ring).inverse.obj
          ((P.finiteReduction m hm hmn Y).obj K)) :
    letI := hasCompactification_of_finiteType_over_field P.field.k X Y f
    let S := (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.obj
      (((smoothPurityTensor P.Coefficient X).obj
        ((P.smoothPurityPullback f).obj
          ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj K))).obj
        (P.diagonalDualizing f))
    letI := P.finiteReductionCompactSupportComparison_isIso m hm hmn f S
      (finiteReduction_thetaFactor_source_ctf (P := P) f d K hK)
    inv (P.finiteReductionCompactSupportComparison m hm hmn f S) ≫
      (P.finiteReduction m hm hmn Y).map
        ((P.smoothCompactSupport f).map (P.finitePurityTheta f K J e) ≫
          P.smoothExceptionalCounit f K) =
      ((P.finiteReductionSetting m hm).smoothCompactSupport f).map
        (P.finiteReductionTensorOmegaComparison m hm hmn f K ≫
          (P.finiteReductionSetting m hm).finitePurityTheta f
            ((P.finiteReduction m hm hmn Y).obj K) J' e') ≫
        (P.finiteReductionSetting m hm).smoothExceptionalCounit f
          ((P.finiteReduction m hm hmn Y).obj K) := by
  sorry

end Morphism
end WeilConjectures.PurityFiniteSetting
