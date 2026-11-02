/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapChartPrefix
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineHelper

/-! # Pre-compact factors of the frame prefix

Source: general-ring smooth purity, proof (3), local frame calculation.
(blueprint: def-sp-general-ring-integration-exponent-local-trace-prefix-precompact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The first two factors of the local frame prefix, before compact comparison: the
base-change exchange of the inverse-frame square followed by the chart coefficient
comparison under the compactly supported direct image.

Source: general-ring smooth purity, proof (3), local frame calculation.
(blueprint: def-sp-general-ring-integration-exponent-local-trace-prefix-precompact). -/
def finiteGeneralRingLocalTracePrefixPreCompact
    (N : ℕ) (hNpos : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hN : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hN)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (V : S.Opens) (eV : VectorBundleZeroSection.Trivialization S d F V) :=
  let _hNpos := hNpos
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).2.1
  letI : TopologicalSpace.NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  letI : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      isCompact_univ := TopologicalSpace.NoetherianSpace.isCompact _ }
  (Etale.rightDerivedLowerShriekBaseChangeMap A
      (Etale.vectorIntegrationChart_isPullback S d F V eV)).app
    (Etale.vectorIntegrationCoefficient A N hN S d F) ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection V.toScheme d)).map
      (Etale.vectorIntegrationChartCoefficient A N hN t S hS d F V eV).hom

end AlgebraicGeometry.ProEtale
