/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions
import Sheaf.Paper.AffineDiagonalDncCoordinateIdentity
import Sheaf.Paper.AffineDiagonalRestrictedTransposes

/-! # Normalized DNC calculation in ordered difference coordinates

Source: smooth-purity, Agreement on the model.
(blueprint: lem-pur-affine-diagonal-dnc-normalization).
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

/-- The DNC half of affine diagonal model agreement, for the specified actual
transposes on the self-product and normal cone. This assertion uses neither the
transpose on X→Y nor the diagonal base-change comparison alpha.
Source: smooth-purity, Agreement on the model, translation and standard-pair normalization.
(blueprint: lem-pur-affine-diagonal-dnc-normalization).

Proof: use the ordered difference coordinates u=y-x on the self-product. The
proved translated-coordinate specification carries the diagonal to zero. The
normal-coordinate specification identifies the intrinsic normal cone with the
same trivial bundle, sending the homogeneous class of each y_i-x_i to v_i. Rees
normalization identifies the deformation coordinates by u_i=t v_i, preserving
the order and sign. Translation invariance of the actual affine integration and
naturality of its exceptional transpose identify J with the standard-bundle
transpose in u coordinates. The DNC family of this standard pair is the constant
family in v coordinates. The normalization and uniqueness of DNC invariance make
its two-fibre arrow the identity on the pulled-back standard section invariant.
Restricting Q inverse along zero is therefore the inverse of restricting J along
the diagonal. Insert the stated source, normal, and Tate restriction comparisons;
these are exactly T and beta, so delta followed by beta equals T inverse. For
rank zero the coordinate lists are empty and the constant-family computation is
unchanged. The constructions and equalities hold over the empty base as well. -/
theorem affineDiagonalDncNormalization (P : PurityFiniteSetting.{u})
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
  let C := fun B : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let δ := (Dnc.existsUnique_dncInvariance P d p₁ aX s (pullback.diagonal_fst p)).exists.choose
  ∀ (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
    (hq : Etale.FiniteSmoothPurity.ReesConeNormalized s q),
    let πN := Scheme.Hom.normalConeProj p₁ s
    let z := s.normalConeZeroSection
    letI := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
    letI := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
    letI := (affineDiagonalNormalCoordinates_spec Y d q hq).1
    letI := (affineDiagonalProductCoordinates_spec Y d).1
    ∀ (J : L W d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p₁)
      (Q : L s.ker.normalCone d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) πN),
      J.hom = P.affineDiagonalPresentedTranspose d p₁ aX r hA
        (asIso (affineDiagonalProductCoordinates Y d))
        (affineDiagonalProductCoordinates_spec Y d).2 →
      Q.hom = P.affineDiagonalPresentedTranspose d πN aX r hA
        (asIso (affineDiagonalNormalCoordinates Y d q))
        (affineDiagonalNormalCoordinates_spec Y d q hq).2 →
      (let T := (C X).mapIso
          ((P.affineDiagonalTateRestriction r hA s (p₁ ≫ aX) d).symm ≪≫
            (F s).mapIso J) ≪≫ (Dnc.sourceComparison P d p₁ aX s).symm
       let β := Dnc.normalComparison P d p₁ aX s (pullback.diagonal_fst p) ≪≫
          (C X).mapIso ((F z).mapIso Q.symm ≪≫
            P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d)
       δ.hom ≫ β.hom = T.inv) := by
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let p₁ := pullback.fst p p
  let s := pullback.diagonal p
  let aX := p ≫ aY
  let := affineDiagonalProjection_smooth Y d
  let := SmoothOfRelativeDimension.smooth d p
  let := Dnc.compactifiable P p aY
  let := Dnc.compactifiable P p₁ aX
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory
  let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let δ := (Dnc.existsUnique_dncInvariance P d p₁ aX s
    (pullback.diagonal_fst p)).exists.choose
  dsimp only
  intro q hq
  let πN := Scheme.Hom.normalConeProj p₁ s
  let z := s.normalConeZeroSection
  let := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
  let := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
  let := (affineDiagonalNormalCoordinates_spec Y d q hq).1
  let := (affineDiagonalProductCoordinates_spec Y d).1
  intro J Q hJ hQ
  let j := (P.affineDiagonalTateRestriction r hA s (p₁ ≫ aX) d).symm ≪≫ (F s).mapIso J
  let n := (P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d).symm ≪≫ (F z).mapIso Q
  let S := C.mapIso (P.affineDiagonalSourceCoordinates Y aY d)
  let N := C.mapIso (P.affineDiagonalNormalSectionCoordinates Y aY d q hq)
  let src := Dnc.sourceComparison P d p₁ aX s
  let nor := Dnc.normalComparison P d p₁ aX s (pullback.diagonal_fst p)
  have hd : δ.hom ≫ nor.hom ≫ N.hom = src.hom ≫ S.hom :=
    P.affineDiagonalDncCoordinateIdentity Y aY d q hq
  have ht : j ≪≫ P.affineDiagonalSourceCoordinates Y aY d =
      n ≪≫ P.affineDiagonalNormalSectionCoordinates Y aY d q hq :=
    P.affineDiagonalRestrictedTransposes Y aY d r hA q hq J Q hJ hQ
  have ht' : (C.mapIso j).hom ≫ S.hom = (C.mapIso n).hom ≫ N.hom := by
    simpa only [S, N, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp] using
      congrArg (fun e ↦ (C.mapIso e).hom) ht
  have hn : nor.hom ≫ (C.mapIso n).inv = δ.inv ≫ src.hom ≫ (C.mapIso j).inv := by
    apply (cancel_mono ((C.mapIso j).hom ≫ S.hom)).mp
    calc
      (nor.hom ≫ (C.mapIso n).inv) ≫ ((C.mapIso j).hom ≫ S.hom) =
          nor.hom ≫ N.hom := by
        rw [ht']
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = δ.inv ≫ src.hom ≫ S.hom := by
        rw [← hd]
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (δ.inv ≫ src.hom ≫ (C.mapIso j).inv) ≫
          ((C.mapIso j).hom ≫ S.hom) := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change δ.hom ≫ (nor ≪≫ C.mapIso
    ((F z).mapIso Q.symm ≪≫ P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d)).hom =
      (C.mapIso j ≪≫ src.symm).inv
  have hb : (F z).mapIso Q.symm ≪≫
      P.affineDiagonalTateRestriction r hA z (πN ≫ aX) d = n.symm := rfl
  rw [hb, Functor.mapIso_symm]
  change δ.hom ≫ (nor.hom ≫ (C.mapIso n).inv) = src.hom ≫ (C.mapIso j).inv
  rw [hn]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end WeilConjectures.PurityFiniteSetting
