/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.FiniteGeneralRingData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Core local trace comparison for finite general-ring integration

Source: general-ring smooth purity, proof (3), Kummer exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The finite-ring Kummer comparison transports the prescribed local affine trace.

Source: general-ring smooth purity, proof (3), exponent independence, projective-line
and ordered affine-line trace comparison on one vector-bundle frame.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace-core).

Proof: compare the two normalized projective-line decompositions using the two clauses
of `FiniteGeneralRingKummerComparison`; use naturality of the open counit and iterate
the ordered affine counit in its prescribed coordinate order.  The inverse-frame and
coefficient comparisons are natural, so the resulting coefficient arrow is the pullback
of `finiteGeneralRingLevelPower`.  This is the local calculation before inserting the
globally normalized vector-bundle integration map.
-/
theorem finiteGeneralRingLocalTraceExponent_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (DN : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A N hN tN T hT)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM)
    (DM : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM tM T hT)
    (V : S.Opens) (eV : VectorBundleZeroSection.Trivialization S d F V) :
    (Etale.ordinaryFinitePullback A V.ι).map
        ((Etale.vectorBundlePurityLower A S d F).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
            (finiteGeneralRingLevelPower A M N hM hN S b d).hom)) ≫
      Etale.vectorIntegrationLocalTrace N hNpos A hN tN DN S hS' d F V eV =
      Etale.vectorIntegrationLocalTrace M hMpos A hM tM DM S hS d F V eV := by
  sorry

end AlgebraicGeometry.ProEtale
