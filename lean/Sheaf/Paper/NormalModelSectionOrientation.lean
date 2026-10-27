/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.DiagonalDncChartNormalization

/-! # Integration normalization on a vector presentation of a section invariant

Source: smooth-purity chart proof, Step 4, and the vector-bundle model agreement.
(blueprint: lem-pur-normal-model-section-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- Presenting a vector bundle by an isomorphic smooth total space preserves its
integration-normalized zero-section orientation, with the actual etale locality
mate and the canonical Tate restriction maps.
Source: sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 4;
sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-vector-bundle.proof.md, Step 3.
(blueprint: lem-pur-normal-model-section-orientation).

Proof: on a frame of F the prescribed integration is the ordered affine-space
trace. Its exceptional adjunction transpose is the inverse coordinate-normalized
orientation, by vector-bundle purity and the affine counit normalization. The
same holds on every frame; remove the even Tate shift and use sheaf Hom gluing
to obtain equality on the bundle. Source-etale restriction of the normalized
orientation along e gives the exceptional-locality mate appearing below.
Invert this equation and pull back along the zero section. The equations w and
hs identify the projection and section; the canonical pullback compositor and
Tate pullback composition identify the remaining factors. The rank-zero trace
is the identity counit, and the empty-base case follows from the empty-cover
sheaf axiom. -/
theorem normalModelSectionOrientation (P : PurityFiniteSetting.{u})
    {B N : Scheme.{u}} [IsNoetherian B] (d : ℕ) (q : N ⟶ B)
    [SmoothOfRelativeDimension d q] [IsSeparated q]
    [LocallyOfFiniteType q] [QuasiCompact q]
    (aB : B ⟶ Spec (.of P.field.k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ N) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (e : VectorBundleZeroSection.scheme B d F ≅ N)
    (w : e.hom ≫ q = VectorBundleZeroSection.π B d F)
    (hs : VectorBundleZeroSection.zero B d F ≫ e.hom = s)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (M : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := P.noetherian aB
    letI := P.noetherian (q ≫ aB)
    letI := (Etale.vectorIntegration_geometry B d F).1
    letI := (Etale.vectorIntegration_geometry B d F).2.1
    letI := P.noetherian (VectorBundleZeroSection.π B d F ≫ aB)
    letI := Dnc.compactifiable P q aB
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π B d F) aB
    ∀ (γ : P.diagonalTwistEtale (VectorBundleZeroSection.scheme B d F) d ≅
        P.diagonalOrdinaryDualizing (VectorBundleZeroSection.π B d F)),
      γ.hom = (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
          P.diagonalExponent P.diagonalExponent_annihilates t
          (VectorBundleZeroSection.π B d F) (P.diagonalExponent_isUnit aB) d).inv ≫
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (VectorBundleZeroSection.π B d F)).homEquiv _ _
            (Etale.vectorBundleIntegration P.diagonalExponent
              (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
              P.diagonalExponent_annihilates B (P.diagonalExponent_isUnit aB) d F) →
      P.chartSectionOrientation d q aB s t =
        P.chartSectionEtaleRestriction M e.hom q
            (VectorBundleZeroSection.π B d F) w s
            (VectorBundleZeroSection.zero B d F) hs ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
            (VectorBundleZeroSection.zero B d F)).leftDerivedFunctor.mapIso
              (P.chartDualizingUnit (VectorBundleZeroSection.π B d F) ≪≫ γ.symm) ≪≫
          Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t (VectorBundleZeroSection.zero B d F)
            (P.diagonalExponent_isUnit (VectorBundleZeroSection.π B d F ≫ aB)) d := by
  sorry

end WeilConjectures.PurityFiniteSetting
