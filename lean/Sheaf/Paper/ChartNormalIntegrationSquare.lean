/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.GeneralChartComparisons

/-! # Naturality of chart normal integration -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- Normal integration commutes with the actual normal differential and the
canonical shifted Tate comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Step 4
(blueprint: lem-pur-chart-normal-integration-square).

Proof: identify the two normal bundles using the actual graded conormal pullback
map. In degree one this is the differential, by the coordinate-difference formula.
On pulled-back coordinate frames vector integration commutes with arbitrary base
change: compact-support exchange and the actual adjunction counits define both
maps. Changing a frame multiplies by a linear bundle automorphism; the ordered
trace is invariant under it. Hence the same equation holds for this differential.
Apply the integration site-comparison theorem, including its tensor and adjoint
normalizations, and cancel the compared normal-bundle model isomorphisms. The
remaining coefficient comparison is precisely pullComparison followed by nu-star
of vectorIntegrationBaseCoefficientPullback, as displayed. In rank zero the trace
and all comparisons are the identity; on the empty scheme the arrow is unique.
No ramification or flatness condition on the coefficient ring is used. -/
theorem chart_normal_integration_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    r P aV e ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (ChartFactors.beta P d B.proj aV N) ≪≫
      (Dnc.pullComparison P e.hom (P.diagonalTwistEtale B.X d) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory.mapIso
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t e.hom
            (P.diagonalExponent_isUnit (B.proj ≫ aV)) d)) =
      ChartFactors.beta P d C.proj aV N := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartComparisons
