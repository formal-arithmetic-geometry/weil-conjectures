/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.FiniteGeneralRingData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Data
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import Sheaf.SecSmoothPurity.FiniteGeneralRingLocalTraceCore

/-! # Local frame comparison for finite general-ring integration

Source: general-ring smooth purity, proof (3), Kummer exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- The Kummer comparison identifies the prescribed local vector-bundle traces.

Source: general-ring smooth purity, proof (3), exponent independence, and proof (2),
the ordered affine-line trace comparison.
(blueprint: lem-sp-general-ring-integration-exponent-local-trace).

Proof: on the chosen frame, expand the vector integration local trace into the inverse-frame
exchange, the normalized Tate coefficient comparison, and the ordered affine counit. The
Kummer power and generator equations in `hb` identify the projective-line Chern and unit
columns, hence identify the normalized projective trace. Naturality of the open-extension
counit and induction on the ordered affine coordinates identify the resulting affine traces.
The frame comparison is exactly the displayed pullback of `finiteGeneralRingLevelPower`.
-/
theorem finiteGeneralRingLocalTraceExponent
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
    (t : Etale.OrdinaryFiniteTwistTransport A M hM)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (M : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum A M hM t T hT)
    (V : S.Opens) (eV : VectorBundleZeroSection.Trivialization S d F V) :
    (Etale.ordinaryFinitePullback A V.ι).map
        ((Etale.vectorBundlePurityLower A S d F).map
          ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
            (finiteGeneralRingLevelPower A M N hM hN S b d).hom) ≫
          Etale.vectorBundleIntegration N hNpos A hN S hS' d F) ≫
        (Etale.ordinaryFiniteUnitPullback A V.ι).hom =
      Etale.vectorIntegrationLocalTrace M hMpos A hM t D S hS d F V eV := by
  obtain ⟨tN, DN, _, _⟩ := Etale.exists_affineSpaceTopTrace N hNpos A hN
  have hnorm : Etale.VectorIntegrationNormalization N hNpos A hN S hS' d F
      (Etale.vectorBundleIntegration N hNpos A hN S hS' d F) := by
    unfold Etale.vectorBundleIntegration Etale.vectorIntegrationGluing
    exact (Etale.existsUnique_vectorIntegrationGluing N hNpos A hN S hS' d F).2.exists.choose_spec.2
  have hnormV := hnorm tN DN V eV
  have hcore := finiteGeneralRingLocalTraceExponent_core A M N hMpos hNpos hdiv
    hM hN S hS hS' d F q b hb tN DN t D V eV
  simp only [Functor.map_comp]
  rw [Category.assoc, hnormV]
  exact hcore

end AlgebraicGeometry.ProEtale
