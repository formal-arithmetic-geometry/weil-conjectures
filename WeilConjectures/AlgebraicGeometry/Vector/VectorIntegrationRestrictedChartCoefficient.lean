/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationCartesianPrefix
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientComposition

/-! # Coefficient comparison for a restricted inverse frame
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Successive inverse-image coefficient identifications for a frame on V and its
restriction to U equal direct coefficient descent in the pasted inverse-chart square.
No compact-support functor or exchange map occurs in this equality. -/
theorem vectorIntegration_restricted_chart_coefficient
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U V : S.Opens) (hUV : U ≤ V)
    (e : VectorBundleZeroSection.Trivialization S d F V) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (affineTraceMap (S.homOfLE hUV) d) (vectorIntegrationChart S d F V e)).hom.app
        (vectorIntegrationCoefficient A N hA S d F) ≫
      (ordinaryFinitePullback A (affineTraceMap (S.homOfLE hUV) d)).map
        (vectorIntegrationChartCoefficient A N hA t S hS d F V e).hom ≫
      (affineTraceRightBaseChange A N hA t (S.homOfLE hUV)
        (affineTracePullbackInvertible N V.ι hS) d (ordinaryFiniteUnit A V.toScheme)).hom ≫
      (affineTraceRight A N hA U.toScheme d).map
        (ordinaryFiniteUnitPullback A (S.homOfLE hUV)).hom =
    (vectorIntegrationCartesianCoefficient A N hA t (VectorBundleZeroSection.π S d F)
      U.ι (affineTracePullbackInvertible N U.ι hS) d
      (vectorIntegrationRestrictedChart S d F U V hUV e)
      (vectorIntegrationRestrictedChart_isPullback S d F U V hUV e)
      (affineLinearBaseCoefficient A N hA S d)
      (vectorIntegrationBaseCoefficientPullback A N hA t U.ι hS d)).hom  := by
  unfold vectorIntegrationCartesianCoefficient vectorIntegrationChartCoefficient
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hb := affineTraceRightBaseChange_unit_coefficient A N hA t
    (S.homOfLE hUV) (affineTracePullbackInvertible N V.ι hS)
      (affineTracePullbackInvertible N U.ι hS) d
  have hb' := congrArg Iso.hom hb
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hb'
  rw [hb']
  simpa only [vectorIntegrationCartesianCoefficient, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] using
    vectorIntegration_restricted_chart_coefficient_composition N hN A hA t S hS d F U V hUV e

end AlgebraicGeometry.Etale
