/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X9
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingData

/-! # Ordinary integration adjunct in a linear frame

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Step 4; the affine-frame normalization
of vector integration in sec-smooth-purity/sk-prop-an/def-amb-vector-integration.
(blueprint: lem-pur-vector-integration-ordinary-frame-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- In one linear frame the actual ordinary vector integration adjunct is the
ordered affine counit mate, with the specified source-etale locality comparisons.
There is no orientation input and no global equality or descent conclusion.
Source: blueprint latest, orientation-charts proof Step 4, and vector integration's
inverse-frame normalization and the affine trace base-change formula.
(blueprint: lem-pur-vector-integration-ordinary-frame-counit).

Proof: evaluate the normalization furnished by existsUnique_vectorIntegrationGluing
at the chosen frame and the same t,D. It expresses restriction of the actual trace
as compact-support exchange for the inverse-frame square, the canonical coefficient
identification, inverse affine compact comparison, and the ordered affine counit.
Transpose this equation under the fixed exceptional adjunction. Naturality of its
Hom equivalence turns compact-support exchange into its exceptional mate. Compose
with normalized source-etale locality on both the bundle and the ambient affine
space; mate pasting cancels their common open-extension counit. Uniqueness of normalized
twist transport and P1 datum supplies the base-change law for the specified t,D. The affine
trace base-change equation along the open inclusion of the frame base identifies the
remaining restricted affine trace with the ambient-base counit. Pullback coherence
for the constant coefficient and shifted Tate line identifies the two sources.
Induction on d proves this coefficient identity: at zero it is constant-unit
pullback composition, and at a successor it follows from tensor pullback composition
and shifted-line pullback composition. The resulting composite is exactly the
right side below. The normalization of t,D fixes the rank-one scalar; no choice of
generator or purity isomorphism enters. At rank zero the ordered adjunction is the
identity; an empty frame has unique maps. The argument uses only an invertible
annihilating exponent and works at arbitrary finite coefficient extensions. -/
theorem vectorIntegration_ordinary_frame_counit (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsAffine S] (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := isNoetherian_of_locallyOfFiniteType aS
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    letI := isNoetherian_of_locallyOfFiniteType (VectorBundleZeroSection.π S d F ≫ aS)
    letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
    letI := affineTraceNoetherian S d
    ∀ (U : S.Opens) [IsAffine U.toScheme]
      (frame : VectorBundleZeroSection.Trivialization S d F U),
      let p := VectorBundleZeroSection.π S d F
      let W := p ⁻¹ᵁ U
      letI := isNoetherian_of_locallyOfFiniteType W.ι
      ∀ (v : W.toScheme ⟶ affineTraceTower S d)
        [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
        (_hv : v = VectorBundleZeroSection.trivializationMap S d F U frame ≫
          AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫ (affineTraceAffineSpaceIso S d).inv)
        (w : v ≫ affineTraceProjection S d = W.ι ≫ p),
        letI : HasCompactification (W.ι ≫ p) := inferInstance
        letI : HasCompactification (v ≫ affineTraceProjection S d) := by
          rw [w]
          infer_instance
        (Etale.ordinaryFinitePullback P.Coefficient W.ι).map
            ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates t p (P.diagonalExponent_isUnit aS) d).inv ≫
            (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
              p).homEquiv _ _
                (Etale.vectorBundleIntegration P.diagonalExponent
                  (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
                  P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)) ≫
            (P.diagonalEtaleLocality N W.ι p).hom =
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t W.ι (P.diagonalExponent_isUnit (p ≫ aS)) d).hom ≫
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t v
              (affineTraceInvertible P.diagonalExponent S (P.diagonalExponent_isUnit aS) d)
                d).inv ≫
          (Etale.ordinaryFinitePullback P.Coefficient v).map
            (P.diagonalAffineMate t D S (P.diagonalExponent_isUnit aS) d) ≫
          (P.diagonalEtaleLocality N v (affineTraceProjection S d)).hom ≫
          (P.diagonalDualizingCongr w).hom := by sorry

end WeilConjectures.PurityFiniteSetting
