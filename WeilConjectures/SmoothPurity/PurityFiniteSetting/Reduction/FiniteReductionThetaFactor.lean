/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionTensorFactors

/-! # Coefficient reduction of the tensor adjunction factor

Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Steps 2–3.
(blueprint: lem-pur-finite-reduction-theta-factor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

/-- Reduction of theta on the original intrinsic object, before inserting any orientation.
Source: blueprint/latest, thm-pur-finite-reduction-of-purity, Step 2
(blueprint: lem-pur-finite-reduction-theta-factor).
Proof: choose bounded flat etale models for K and its coefficient reduction; the
reduced model has the same Tor interval. Apply finite_adjoint_mate_tensor to the
etale origin and the actual quotient map. The ordinary coefficient unit maps to
the quotient unit, so the unit-normalized version is the smoothPurityEtaleTheta
square. Transport it through the etale/pro-etale tensor and pullback comparisons.
Their scalar comparison is the mate of restriction's sectionwise identity square.
After conjugation by the two origin isomorphisms and realization counits, tensor
balancing is finiteReductionTensorOmegaComparison: its omega factor is the
presented exceptional-unit mate omegaMap. The target exceptional comparison has
the reduced counit as transpose, hence is finiteReductionExceptionalComparison by
its uniqueness theorem. Naturality and the triangle identities cancel the origin
and realization units. This gives the displayed equation for every pair of
presentations. No diagonal orientation, Tate-line map, or purity map enters it. -/
theorem finiteReduction_thetaFactor (d : ℕ) [SmoothOfRelativeDimension d f]
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
    (P.finiteReduction m hm hmn X).map (P.finitePurityTheta f K J e) ≫
        P.finiteReductionExceptionalComparison m hm hmn f d K hK =
      P.finiteReductionTensorOmegaComparison m hm hmn f K ≫
        (P.finiteReductionSetting m hm).finitePurityTheta f
          ((P.finiteReduction m hm hmn Y).obj K) J' e' := by sorry

end Morphism
end WeilConjectures.PurityFiniteSetting
