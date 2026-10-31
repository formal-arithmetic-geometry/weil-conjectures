/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelAffineIntegrationOrientationNormalized

/-! # Intermediate direct-sum integration equations -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The orientation map produced by the normalized direct-sum integration calculation,
written in the general model-orientation coordinates.  This is the coefficient-unit
map before identifying the affine coordinate model with the canonical diagonal model.
Source: latest blueprint, composition proof Step 1.
(blueprint: new-pur-affine-integration-direct-sum-model-formula).
-/
def affineDirectSumModelMap (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [IsSeparated (DiagonalPasting.q d e B)]
    [LocallyOfFiniteType (DiagonalPasting.q d e B)]
    [QuasiCompact (DiagonalPasting.q d e B)]
    [SmoothOfRelativeDimension d (DiagonalPasting.q d e B)]
    [IsSeparated (DiagonalPasting.pr e B)]
    [LocallyOfFiniteType (DiagonalPasting.pr e B)]
    [QuasiCompact (DiagonalPasting.pr e B)]
    [SmoothOfRelativeDimension e (DiagonalPasting.pr e B)] :=
  (P.compatibleTensorIso
    (P.modelOrientation d (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (DiagonalPasting.q d e B)).leftDerivedFunctor.mapIso
      (P.modelOrientation e (DiagonalPasting.pr e B) aB))).hom ≫
    (P.modelOrientationMu d e (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)).hom

/-- The normalized vector-integration direct-sum calculation gives the coefficient-unit
formula for the total affine projection, in the general model-orientation coordinates.
Source: latest blueprint, composition proof Step 1 (direct-sum compatibility of normalized
orientations).
(blueprint: new-pur-affine-integration-direct-sum-model-formula).

Proof: for a trivial rank-r bundle u over an affine finite-type base write G(u) for the
coefficient-unit component of its integration transpose. The ordered-integration theorem and
coefficient-counit normalization identify the integration transpose with theta(u,-) composed
with the tensor of the identity and G(u); projection purity agreement and the ordered
normalization of the canonical family identify G(u) with the inverse diagonal orientation,
for q (a trivial rank-d bundle over the affine A^e) as for the coordinate projections.
Apply normalized direct-sum compatibility of vector integration to the coordinate bundles of
ranks d and e at the unit coefficient, with f = q, g = pr_e and h = pr_(d+e) = q pr_e.
Vector-integration site comparison transports trace, projection and exceptional transpose to
the pro-etale site; compact-support site coherence and mate pasting identify its compositor
with the recorded pro-etale one. This gives G(h) after concatenation as c-inverse composed with
theta(q, omega(pr_e)) and the pullback of G(pr_e). Move G(pr_e) through theta by naturality
and use the tensor symmetry in sigma: sigma followed by the total orientation equals the tensor
of the diagonal orientations of q and pr_e followed by Tate concatenation, which is
affineDirectSumModelMap. At rank zero the ordered comparison reduces to unit constraints;
empty bases give zero categories.
-/
theorem affine_integration_directSum_model_formula (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.1
    letI := (DiagonalPasting.affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := DiagonalPasting.affineDimension e B
    letI := Dnc.compactifiable P (DiagonalPasting.pr e B) aB
    letI := Dnc.compactifiable P (DiagonalPasting.q d e B)
      (DiagonalPasting.pr e B ≫ aB)
    ProEtale.CompositionTensorMate.sigma P.Coefficient
        (DiagonalPasting.q d e B) (DiagonalPasting.pr e B) ≫
      (P.modelAffineTotalOrientation P.modelAffineCanonicalGamma B d e aB).hom =
      affineDirectSumModelMap P B d e aB := by
  sorry

end WeilConjectures.PurityFiniteSetting
