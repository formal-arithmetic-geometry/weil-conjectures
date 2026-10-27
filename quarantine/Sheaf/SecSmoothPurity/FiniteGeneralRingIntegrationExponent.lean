/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.FiniteGeneralRingData

/-! # Kummer exponent comparison of the vector-bundle integration

Source: general-ring smooth purity, proof (3), Kummer exponent independence.
(blueprint: lem-sp-general-ring-integration-exponent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- A root-normalized Kummer exponent comparison preserves actual vector-bundle
integration, before taking an adjunction transpose or restricting to the zero section.

Source: general-ring smooth purity, proof (3), exponent independence, and proof (2),
the Kummer projective-line normalization and vector-bundle integration step.
(blueprint: lem-sp-general-ring-integration-exponent).

Proof: write M = N times k. The morphism from the M-Kummer sequence to the N-Kummer
sequence has k-th power on the units term containing the roots, and identity on
the last units term. Boundary naturality sends the M-boundary of O(1) to its
N-boundary. After extension to A, the scalar/root generator equation for b
identifies the two Chern classes. The projective-line decomposition has these
Chern classes as its second columns and the twisted units as its first columns.
Naturality of the unit and normalized Tate pullback identifies the first columns.
Thus the decompositions, their inverses and second-projection traces commute with
the root-line comparison. Naturality of the open-extension counit gives the same
identity on the affine line. Iterate in the prescribed coordinate order, using
counit naturality at each step: the zero-coordinate transition and counit are
identities; at a successor the counit is the preceding counit after the preceding
left functor applied to the last affine-line counit. This proves the ordered
affine trace identity without permuting factors. On each frame of F the actual
bundle integration restricts to this affine trace after inverse-frame exchange
and normalized Tate pullback. Those comparisons are natural on scalar/root
generators, so the coefficient map in this identity is exactly pullback of
finiteGeneralRingLevelPower. The equations on all frames identify the global
integration maps: the sources have only degree-zero cohomology by the affine
trace isomorphism, so derived single full faithfulness reduces the equality to
sheaf-Hom equality, detected by the frame cover. This includes the empty cover
on an empty scheme. At rank zero the tensor and the counit are identities; for
the zero ring every displayed morphism is the unique morphism.
-/
theorem finiteGeneralRingIntegrationExponent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N) (hdiv : N ∣ M)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b) :
    (Etale.vectorBundlePurityLower A S d F).map
        ((Etale.ordinaryFinitePullback A (VectorBundleZeroSection.π S d F)).map
          (finiteGeneralRingLevelPower A M N hM hN S b d).hom) ≫
        Etale.vectorBundleIntegration N hNpos A hN S hS' d F =
      Etale.vectorBundleIntegration M hMpos A hM S hS d F := by
  sorry

end AlgebraicGeometry.ProEtale
