/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.Paper.AffineDiagonalIntegrationConstructions

import Sheaf.Paper.AffineDiagonalPresentedBaseChange
import Sheaf.AlgebraicGeometry.OrderedTateSectionPullback
import Sheaf.Paper.SectionCoordinateCounitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.SixFunctors.Etale.Derived.WeilOperations

/-! # Trace and diagonal restriction for affine integration

Source: smooth-purity, Agreement on the model.
(blueprint: lem-pur-affine-diagonal-trace-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] affineDiagonalNormalCoordinates
  affineDiagonalNormalFunction affineDiagonalDifferenceLift
  affineDiagonalProductCoordinates affineDiagonalPresentedTranspose
  affineDiagonalTateRestriction
  Etale.FiniteSmoothPurity.ReesConeNormalized
  Etale.affineLinearCompactComparison
  Etale.ambientAffineTraceTransport Etale.ambientAffineTraceDatum
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

private theorem presentedTranspose_isIso (P : PurityFiniteSetting.{u})
    {U B : Scheme.{u}} (d : ℕ) (f : U ⟶ B) [HasCompactification f] [QuasiCompact f]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0)
    (e : U ≅ affineTraceTower B d) (he : e.hom ≫ affineTraceProjection B d = f) :
    IsIso (P.affineDiagonalPresentedTranspose d f aB r hA e he) := by
  let := P.noetherian aB
  let N := P.coefficients.l ^ (r + 1)
  let hN := pow_pos P.coefficients.prime.out.pos (r + 1)
  let t := Etale.ambientAffineTraceTransport N hN P.Coefficient hA
  let D := Etale.ambientAffineTraceDatum N hN P.Coefficient hA
  let hB := PurityConventions.coefficientPower_isUnit P B aB r
  have hz := (Etale.affineCoordinateCounit_baseChange N hN P.Coefficient hA
    t D B hB d).1
  have hu : (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).hom =
      𝟙 _ := by
    apply (cancel_mono
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) B).inv).mp
    rw [Iso.hom_inv_id, Category.id_comp, Etale.singleFunctorObjUnitIso_inv]
    rfl
  unfold Etale.CoordinateCounitArrows.towerAdjoint at hz
  erw [hu, Category.comp_id] at hz
  let := affineTraceNoetherian B d
  let sq : IsPullback e.hom f (affineTraceProjection B d) (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id f).symm⟩
  have := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isIso P.Coefficient sq
  have := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    inferInstance
  unfold affineDiagonalPresentedTranspose
  dsimp only
  infer_instance

set_option linter.unusedVariables false in
/-- The trace half of affine diagonal model agreement: actual integration
transposes are invertible, commute with the self-product base change, and restrict
along the diagonal to the original transpose. No DNC comparison occurs here.
Source: smooth-purity, Agreement on the model, trace comparison and diagonal restriction.
(blueprint: lem-pur-affine-diagonal-trace-restriction).

Proof: all coordinate projections are smooth separated affine bundles over the
Noetherian finite-type base. The ordered affine counit is invertible. Vector-bundle
purity, its unit-input projection formula, and the specified Tate/site comparisons
therefore make each presented transpose invertible; take its asIso to obtain I, J,
and Q. Apply the affine-space counit base-change equation to p:X→Y. Transport it
through the canonical compact-support and coefficient comparisons, and apply the
exceptional adjunction Hom bijection. Its mate is exactly the displayed B, giving
the equality for J. Pull back this equality along the diagonal. In the definition
of alpha the pullback of inverse B cancels the pullback of B. The natural pullback
composition comparison and p₂ composed with the diagonal equal to the identity
identify the remaining arrow with I. No coordinate permutation is made. The same
construction uses the normal-coordinate isomorphism for Q. At rank zero these are
identity towers; all formulas also apply over the empty scheme. -/
theorem affineDiagonalTraceRestriction (P : PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : P.Coefficient) = 0) :
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let W := pullback p p
  let p₁ := pullback.fst p p
  let p₂ := pullback.snd p p
  let s := pullback.diagonal p
  let aX := p ≫ aY
  letI := affineDiagonalProjection_smooth Y d
  letI := SmoothOfRelativeDimension.smooth d p
  letI := Dnc.compactifiable P p aY
  letI := Dnc.compactifiable P p₁ aX
  letI := (P.comparedDiagonalBaseChange d p aX aY rfl).2.2.2.1
  let L := Etale.affineLinearBaseCoefficient P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
  let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let C := fun B : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let B := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback p p).flip
  let α := Dnc.sourceComparison P d p₁ aX s ≪≫
    (C X).mapIso (P.diagonalComparedRestriction p (asIso B))
  ∀ (q : s.ker.normalCone ≅ PurityNormalBundle.normalCone s)
    (hq : Etale.FiniteSmoothPurity.ReesConeNormalized s q),
    let πN := Scheme.Hom.normalConeProj p₁ s
    let z := s.normalConeZeroSection
    letI := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
    letI := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
    letI := (affineDiagonalNormalCoordinates_spec Y d q hq).1
    letI := (affineDiagonalProductCoordinates_spec Y d).1
    ∃ (I : L X d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p)
      (J : L W d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p₁)
      (Q : L s.ker.normalCone d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) πN),
      I.hom = P.affineDiagonalPresentedTranspose d p aY r hA (Iso.refl X)
        (Category.id_comp p) ∧
      J.hom = P.affineDiagonalPresentedTranspose d p₁ aX r hA
        (asIso (affineDiagonalProductCoordinates Y d))
        (affineDiagonalProductCoordinates_spec Y d).2 ∧
      Q.hom = P.affineDiagonalPresentedTranspose d πN aX r hA
        (asIso (affineDiagonalNormalCoordinates Y d q))
        (affineDiagonalNormalCoordinates_spec Y d q hq).2 ∧
      (C W).map J.hom = (C W).map
        ((P.affineDiagonalTateRestriction r hA p₂ aX d).inv ≫
          (F p₂).map I.hom ≫ B) ∧
      (let T := (C X).mapIso
          ((P.affineDiagonalTateRestriction r hA s (p₁ ≫ aX) d).symm ≪≫
            (F s).mapIso J) ≪≫ (Dnc.sourceComparison P d p₁ aX s).symm
       T.hom ≫ α.hom = (C X).map I.hom) := by
  let p := affineDiagonalProjection Y d
  let X := affineDiagonalSpace Y d
  let W := pullback p p
  let p₁ := pullback.fst p p
  let p₂ := pullback.snd p p
  let s := pullback.diagonal p
  let aX := p ≫ aY
  let := affineDiagonalProjection_smooth Y d
  let := SmoothOfRelativeDimension.smooth d p
  let := Dnc.compactifiable P p aY
  let := Dnc.compactifiable P p₁ aX
  let := (P.comparedDiagonalBaseChange d p aX aY rfl).2.2.2.1
  let L := Etale.affineLinearBaseCoefficient P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
  let F := fun {U B : Scheme.{u}} (f : U ⟶ B) ↦
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor
  let C := fun B : Scheme.{u} ↦
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory
  let B := Etale.dualizingComplexBaseChangeMap P.Coefficient
    (IsPullback.of_hasPullback p p).flip
  dsimp only
  intro q hq
  let πN := Scheme.Hom.normalConeProj p₁ s
  let := Dnc.normalQuasiCompact d p₁ s (pullback.diagonal_fst p)
  let := Dnc.normalCompactifiable P d p₁ aX s (pullback.diagonal_fst p)
  let := (affineDiagonalNormalCoordinates_spec Y d q hq).1
  let := (affineDiagonalProductCoordinates_spec Y d).1
  have hi := presentedTranspose_isIso P d p aY r hA (Iso.refl X) (Category.id_comp p)
  have hj := presentedTranspose_isIso P d p₁ aX r hA
    (asIso (affineDiagonalProductCoordinates Y d))
    (affineDiagonalProductCoordinates_spec Y d).2
  have hq' := presentedTranspose_isIso P d πN aX r hA
    (asIso (affineDiagonalNormalCoordinates Y d q))
    (affineDiagonalNormalCoordinates_spec Y d q hq).2
  let I : L X d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p :=
    asIso (P.affineDiagonalPresentedTranspose d p aY r hA (Iso.refl X)
      (Category.id_comp p))
  let J : L W d ≅ Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) p₁ :=
    asIso (P.affineDiagonalPresentedTranspose d p₁ aX r hA
      (asIso (affineDiagonalProductCoordinates Y d))
      (affineDiagonalProductCoordinates_spec Y d).2)
  let Q : L s.ker.normalCone d ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) πN :=
    asIso (P.affineDiagonalPresentedTranspose d πN aX r hA
      (asIso (affineDiagonalNormalCoordinates Y d q))
      (affineDiagonalNormalCoordinates_spec Y d q hq).2)
  have hbc : J.hom = (P.affineDiagonalTateRestriction r hA p₂ aX d).inv ≫
      (F p₂).map I.hom ≫ B :=
    P.affineDiagonalPresentedTranspose_selfBaseChange Y aY d r hA
  refine ⟨I, J, Q, rfl, rfl, rfl, congrArg (C W).map hbc, ?_⟩
  have hsec := Etale.orderedTateSectionPullback P.Coefficient
    (P.coefficients.l ^ (r + 1)) hA
    (Etale.ambientAffineTraceTransport (P.coefficients.l ^ (r + 1))
      (pow_pos P.coefficients.prime.out.pos (r + 1)) P.Coefficient hA)
    p₂ s (pullback.diagonal_snd p)
    (PurityConventions.coefficientPower_isUnit P X aX r)
    (PurityConventions.coefficientPower_isUnit P W (p₁ ≫ aX) r) d
  have hn := (Etale.leftDerivedUpperStarCompSectionIso
    (ModuleCat.{u + 1} P.Coefficient) s p₂ (pullback.diagonal_snd p)).hom.naturality I.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← (C X).map_comp]
  apply congrArg (C X).map
  unfold diagonalComparedRestriction
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, asIso_inv,
    Category.assoc]
  rw [hbc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (F s).map_comp_assoc B (inv B), IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hn]
  simpa only [affineDiagonalTateRestriction, Etale.ordinaryFinitePullback,
    F, L, s, X, p, aX, p₁, p₂, affineDiagonalSpace, Category.assoc, Category.id_comp] using
    congrArg (fun k ↦ k ≫ I.hom) hsec

end WeilConjectures.PurityFiniteSetting
