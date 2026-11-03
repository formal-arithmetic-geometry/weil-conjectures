/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingBundleSectionOrientationData
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionOrientationMapExt
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionPurityUnitIsIso
import WeilConjectures.AlgebraicGeometry.VectorTraceGeometry.VectorTraceGeometry
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionRankZeroAffineNormalization
import WeilConjectures.AlgebraicGeometry.Bundle.BundleSectionComparisonIsoPasting

/-! # Finite-ring orientations along bundle zero sections

The canonical integration mate constructs the orientation. Its affine normalization
and equality detection on affine frames give existence and uniqueness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem normalized_orientation_eq (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (o o' : bundleSectionObject A S d M ≅ affineLinearBaseCoefficient A N hA S d)
    (ho : BundleSectionOrientationNormalization N hN A hA S hS d M o)
    (ho' : BundleSectionOrientationNormalization N hN A hA S hS d M o') : o = o' := by
  obtain ⟨t, D, _, _⟩ := exists_affineSpaceTopTrace N hN A hA
  have h : o.inv = o'.inv := by
    apply bundleSectionOrientation_map_ext N hN A hA S hS d M
    intro V hV e
    exact (ho t D V hV e).trans (ho' t D V hV e).symm
  have he : o.symm = o'.symm := Iso.ext h
  exact congrArg Iso.symm he

/-- Identity normalization in rank zero, with the canonical geometric identification.
Source: orientation-charts Step 4 (blueprint: lem-trf-finite-ring-bundle-section-orientation).

Proof: the rank-zero symmetric algebra is the structure algebra and augmentation is the
identity. Thus pi and z are inverse. The coordinate tower, counit and its adjunct are the
identity in dimension zero. The normalization on every frame and unique gluing identify
o with the displayed identity-adjunction comparison (node proof Step 8). -/
theorem finiteRingBundleSectionOrientation_rankZero (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (M : S.Modules) [M.IsFiniteLocallyFreeOfRank 0]
    (o : bundleSectionObject A S 0 M ≅ affineLinearBaseCoefficient A N hA S 0)
    (_ho : BundleSectionOrientationNormalization N hN A hA S hS 0 M o) :
    ∃ (e : VectorBundleZeroSection.scheme S 0 M ≅ S)
      (_hp : e.hom = VectorBundleZeroSection.π S 0 M)
      (hz : e.inv = VectorBundleZeroSection.zero S 0 M),
      o.hom = bundleSectionRankZeroComparison A S M e hz := by
  have := VectorTraceGeometry.zero_isIso S M
  let e := asIso (VectorBundleZeroSection.π S 0 M)
  have hz : e.inv = VectorBundleZeroSection.zero S 0 M := by
    apply (cancel_mono (VectorBundleZeroSection.π S 0 M)).1
    exact e.inv_hom_id.trans (VectorBundleZeroSection.zero_spec S 0 M).1.symm
  have : IsIso (VectorBundleZeroSection.zero S 0 M) := hz ▸ e.isIso_inv
  have hb := isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion A
    (IsPullback.of_horiz_isIso
      (CommSq.mk ((VectorBundleZeroSection.zero_spec S 0 M).1.trans
        (Category.comp_id _).symm)))
  have : IsIso (bundleSectionRankZeroComparison A S M e hz) := by
    dsimp only [bundleSectionRankZeroComparison, bundleSectionComparison]
    infer_instance
  let c : bundleSectionObject A S 0 M ≅ affineLinearBaseCoefficient A N hA S 0 :=
    asIso (bundleSectionRankZeroComparison A S M e hz)
  have hc : BundleSectionOrientationNormalization N hN A hA S hS 0 M c := by
    intro t D V hV f
    exact bundleSectionRankZero_affineNormalization N hN A hA S hS M e rfl hz
      t D V hV f
  refine ⟨e, rfl, hz, ?_⟩
  exact congrArg Iso.hom (normalized_orientation_eq N hN A hA S hS 0 M o c _ho hc)

end AlgebraicGeometry.Etale
