/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteReductionThetaFactorTransposeNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteReductionThetaFactorProjectionReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteReductionThetaFactorSourceCtf
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

/-- Equality of the two counit transposes, assembled from separate steps.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 2--4
(blueprint: lem-pur-finite-reduction-theta-factor-mate).

Proof: source constructibility makes the compact-support scalar comparison
invertible. The transpose normalization lemma computes the left side as
q_C.inv followed by Q_Y of the original counit composite. The reduced projection
lemma identifies this middle arrow with the right side. Transitivity of these
two equalities proves the assertion. No new adjunction cancellation occurs here.
-/
theorem finiteReduction_thetaFactor_mate (d : ℕ) [SmoothOfRelativeDimension d f]
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
    (((P.finiteReductionSetting m hm).smoothCompactSupport f).map
      ((P.finiteReduction m hm hmn X).map (P.finitePurityTheta f K J e) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK) ≫
      (P.finiteReductionSetting m hm).smoothExceptionalCounit f
        ((P.finiteReduction m hm hmn Y).obj K)) =
    (((P.finiteReductionSetting m hm).smoothCompactSupport f).map
      (P.finiteReductionTensorOmegaComparison m hm hmn f K ≫
        (P.finiteReductionSetting m hm).finitePurityTheta f
          ((P.finiteReduction m hm hmn Y).obj K) J' e') ≫
      (P.finiteReductionSetting m hm).smoothExceptionalCounit f
        ((P.finiteReduction m hm hmn Y).obj K)) := by
  let := hasCompactification_of_finiteType_over_field P.field.k X Y f
  have hS := finiteReduction_thetaFactor_source_ctf (P := P) f d K hK
  exact (P.finiteReduction_thetaFactor_transpose_normalization m hm hmn f d K hK
    _ hS (P.finitePurityTheta f K J e)).trans
      (P.finiteReduction_thetaFactor_projection_reduction m hm hmn f d K hK J e J' e')
end Morphism
end WeilConjectures.PurityFiniteSetting
