/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleMilnor
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! Canonical normalized-tower effectivity: a step of the current coefficient-fiber proof. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The scalar adjoints of the projections are components of one derived tower map.
Source: latest blueprint, lem-coef-normalized-dvr-effectivity.proof.md, final paragraph,
and sk-lem-sp-tower/_section.md, reduction/limit adjunction
(blueprint: lem-coef-sp-dvr-projection-descent).

Proof: on ordinary modules, extending a module to every quotient is left adjoint to
the limit after scalar restriction. A family of scalar adjoints is a strict tower map
exactly when its adjoints commute with the original transitions; check this on local
pure tensor generators using R.transition. Derive this adjunction with K-flat source
resolutions and K-injective tower resolutions, identifying its right derived functor
with the strict Roos fiber by exact pro-etale products. R.universal identifies the
left functor with R.red, preserving R.counit. Evaluation of this identification is
R.evaluation: on a K-flat representative their counit equations coincide by
R.evaluation_normalized, and localization uniqueness extends that equality to every
object. The adjoint of the identity on the limit is thus a map f with the displayed
component formula. The exact evaluation factors give spDVRLevelLocalization and the
restriction composition gives spDVRFiniteComparison. This construction uses neither
normalization nor any invertibility of those components. It includes the zero tower
and the empty scheme. Compatibility of maps only in the derived level categories is
not used to assert a lift without this resolution construction. -/
theorem normalized_dvr_projection_descent
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
    ∃ f : R.red.obj (spDVRLimit l E T D R P) ⟶ (spTowerLocalization l E T D).obj P,
      ∀ n : ℕ,
        (spDerivedCoefficientEvaluation l E T D n).map f ≫
            (spDVRLevelLocalization l E T D P n).hom =
          (R.evaluation n).hom.app (spDVRLimit l E T D R P) ≫
            spDVRFiniteComparison l E T D R P n := by
  sorry

end AlgebraicGeometry.ProEtale
