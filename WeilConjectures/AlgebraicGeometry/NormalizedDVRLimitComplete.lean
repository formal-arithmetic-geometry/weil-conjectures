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

/-- The specified effectivity isomorphism makes the integral limit derived complete.
Source: latest blueprint, lem-coef-normalized-dvr-effectivity.proof.md, paragraph 5;
def-pe-derived-complete (blueprint: lem-coef-sp-dvr-limit-complete).

Proof: let M be the integral Roos limit of P. The supplied isomorphism e identifies
its derived quotient tower with P. The equation he identifies its components with the
scalar adjoints of the actual Roos projections, so this identification preserves the
coefficient augmentations, not just the isomorphism classes of the levels. Take its
derived limit. The composite from M to the limit of its quotient tower and then to the
limit of P is the identity of M: its projections are precisely those defining M.
Thus the canonical completion map is invertible. For the coefficient tower itself,
the ordinary limit of (A_n)_T is O_{E,T} by sk-prop-sfb-qlbar-colimit-x. On a weakly
contractible quasi-compact pro-etale basis object its transitions are surjective on
sections: lift each locally constant finite-quotient-valued function along the next
quotient. The epimorphic Milnor result gives vanishing R¹lim, so the derived coefficient
limit is O_{E,T} in degree zero. This fixes the coefficient identification in the
completion map. Transport the quotient tower, its augmentations, and this identity
through the section/internal equivalence and integralPointMon_eq. Its completion map
is the one defining IsDerivedComplete of spDVRCompletedLimit. This is exactly the
blueprint's effectivity-to-completeness step; normalization is used in constructing e
upstream, and is not replaced by a per-level torsion or double Roos argument here.
The zero tower and the empty scheme give the same identity, with no boundedness or
constructibility assumption. -/
theorem normalized_dvr_limit_complete
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (P : CochainComplex (spCoefficientTowers l E T) ℤ)
    (e : R.red.obj (spDVRLimit l E T D R P) ≅ (spTowerLocalization l E T D).obj P)
    (he : ∀ n : ℕ,
      (spDerivedCoefficientEvaluation l E T D n).map e.hom ≫
          (spDVRLevelLocalization l E T D P n).hom =
        (R.evaluation n).hom.app (spDVRLimit l E T D R P) ≫
          spDVRFiniteComparison l E T D R P n) :
    IsDerivedComplete l E T (spDVRCompletedLimit l E T D R P) := by
  sorry

end AlgebraicGeometry.ProEtale
