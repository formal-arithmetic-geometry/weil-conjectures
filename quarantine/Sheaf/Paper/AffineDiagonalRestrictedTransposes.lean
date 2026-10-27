/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.AffineDiagonalSectionCoordinates

/-! # Restricted affine integration transposes in geometric section coordinates

Source: smooth-purity, Agreement on the model, translation of the diagonal.
(blueprint: lem-pur-affine-diagonal-restricted-transposes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  Etale.FiniteSmoothPurity.ReesConeNormalized
  Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback
  affineDiagonalSectionCoordinates affineDiagonalSourceCoordinates
  affineDiagonalNormalSectionCoordinates

/-- The two restricted actual integration transposes have the same geometric
standard-section coordinates. This is an ordinary etale equation independent of
any DNC arrow or family trivialization.
Source: latest blueprint, smooth-purity, Agreement on the model, translation
invariance of the normalized affine integration and naturality of its transpose.
(blueprint: lem-pur-affine-diagonal-restricted-transposes).

Proof: first present W as the trivial bundle by the y coordinates. Its difference
coordinates are that presentation followed by translation by minus the tautological
x-vector. The affine translation trace theorem identifies the actual normalized
trace before and after this translation, including its Tate pullback identification.
Transpose this equality through the compact-support adjunction. Naturality of its
Hom bijection identifies the translated transpose with the canonical exceptional
base-change mate used in affineDiagonalSectionCoordinates. Restrict to the diagonal;
its translated image is zero. Thus the left composite is the restriction of the
standard trivial-bundle transpose at zero. The normal-coordinate presentation is
an isomorphism over X preserving zero. The definition of affineDiagonalPresentedTranspose
and the same mate-pasting formula identify the right composite with that very
standard zero restriction. All coefficient comparisons are the specified pure-root
pullback comparisons; no choice of orientation is made. Equality on hom maps gives
equality of the displayed isomorphisms. At rank zero use the identity tower
adjunction; on the empty base the same functorial identities hold. -/
theorem affineDiagonalRestrictedTransposes (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
    let p := affineDiagonalProjection Y d
    let X := affineDiagonalSpace Y d
    let W := pullback p p
    let p₁ := pullback.fst p p
    let s := pullback.diagonal p
    let aX := p ≫ aY
    letI := affineDiagonalProjection_smooth Y d
    letI := SmoothOfRelativeDimension.smooth d p
    letI := Dnc.compactifiable P p aY
    letI := Dnc.compactifiable P p₁ aX
    let L := Etale.affineLinearBaseCoefficient P.Coefficient
      (P.coefficients.l ^ (r + 1)) hA
    let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
    ∀ (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
      (hq : Etale.FiniteSmoothPurity.ReesConeNormalized s q),
      let πN := Scheme.Hom.normalConeProj p₁ s
      let z := s.normalConeZeroSection
      letI := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
      letI := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
      letI := (affineDiagonalNormalCoordinates_spec Y d q hq).1
      letI := (affineDiagonalProductCoordinates_spec Y d).1
      ∀ (J : L W d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p₁)
        (Q : L s.ker.normalCone d ≅
          Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) πN),
        J.hom = P.affineDiagonalPresentedTranspose d p₁ aX r hA
          (asIso (affineDiagonalProductCoordinates Y d))
          (affineDiagonalProductCoordinates_spec Y d).2 →
        Q.hom = P.affineDiagonalPresentedTranspose d πN aX r hA
          (asIso (affineDiagonalNormalCoordinates Y d q))
          (affineDiagonalNormalCoordinates_spec Y d q hq).2 →
        ((P.affineDiagonalTateRestriction r hA s (p₁ ≫ aX) d).symm ≪≫
          (F s).mapIso J) ≪≫ P.affineDiagonalSourceCoordinates Y aY d =
        ((P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d).symm ≪≫
          (F z).mapIso Q) ≪≫ P.affineDiagonalNormalSectionCoordinates Y aY d q hq := by sorry

end WeilConjectures.PurityFiniteSetting
