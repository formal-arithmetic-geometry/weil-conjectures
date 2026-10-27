/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientationData

/-! # Local normalization of the identity-adjunction comparison in rank zero -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- The inverse identity-adjunction comparison has the prescribed affine-frame restriction.
Source: orientation-charts proof Step 4, identity normalization in rank zero.
(blueprint: lem-trf-bundle-section-rank-zero-affine-normalization).

Proof: in rank zero affineTraceTower T 0 and affineTraceProjection T 0 are T and its
identity. The ordered adjunction is Adjunction.id, and its counit is the identity.
The inverse frame carries the zero section to the identity, because its composite with
that projection is the identity. Paste the frame square with the square identifying the
bundle projection with the identity via e. The compact-support exchange pasting and
identity laws identify their exceptional mates. Under the pullback identity unitor,
conjugating the identity compact-support comparison gives precisely
bundleSectionRankZeroComparison. The zero-stage coefficient descent is the pullback
identity comparison, and the zero-stage base coefficient comparison is the constant-unit
pullback comparison. Substituting these into the pasted mate equation gives the displayed
inverse-map normalization. This is an equation on one arbitrary affine frame, and asserts
neither the existence of e nor equality with an arbitrary normalized orientation. The
identity and pasting laws also apply over empty schemes and to zero coefficient rings.
-/
theorem bundleSectionRankZero_affineNormalization (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
    (hp : e.hom = VectorBundleZeroSection.π S 0 M)
    (hz : e.inv = VectorBundleZeroSection.zero S 0 M)
    [IsIso (bundleSectionRankZeroComparison A S M e hz)]
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (V : S.Opens) (hV : IsAffine V.toScheme)
    (f : VectorBundleZeroSection.Trivialization S 0 M V) :
    (ordinaryFinitePullback A V.ι).map
        (inv (bundleSectionRankZeroComparison A S M e hz)) ≫
        bundleSectionChartComparison A S 0 M V f =
      (vectorIntegrationBaseCoefficientPullback A N hA t V.ι hS 0).hom ≫
        (bundleSectionChartCoefficient N A hA t S hS 0 M V f).inv ≫
        (ordinaryFinitePullback A (bundleSectionChartZero S 0 M V f)).map
          (bundleSectionAffineAdjunct N hN A hA t D V.toScheme
            (affineTracePullbackInvertible N V.ι hS) 0) := by sorry

end AlgebraicGeometry.Etale
