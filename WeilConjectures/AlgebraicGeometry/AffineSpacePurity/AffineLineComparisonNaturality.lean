/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurity.AffineSpacePurityComparison
import WeilConjectures.AlgebraicGeometry.OrderedAffineTranspose.OrderedAffineComparisonNaturality

/-! # Naturality of the normalized affine-line comparison

Source: current blueprint, projection-purity agreement, final canonical reassociation;
expanded ordered-transpose proof Step 8.
(blueprint: lem-pur-affine-line-comparison-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.singleFunctors

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

section TensorNormalization
universe v w v' w'
variable {Cat : Type v} {Cat' : Type v'} [Category.{w} Cat] [Category.{w'} Cat']

end TensorNormalization

end AlgebraicGeometry.ProEtale.AffineSpacePurity

namespace AlgebraicGeometry.ProEtale.AffineSpacePurity

private def normalizedTensorIso (B : Cat' ⥤ Cat' ⥤ Cat')
    (H F : Cat ⥤ Cat') (J : Cat ⥤ Cat)
    (a : H ≅ J ⋙ F) (b : J ≅ 𝟭 Cat) {W V : Cat'} (e : W ≅ V) :
    H ⋙ B.flip.obj W ≅ F ⋙ B.flip.obj V :=
  Functor.isoWhiskerRight
    (a ≪≫ Functor.isoWhiskerRight b F ≪≫ Functor.leftUnitor F) (B.flip.obj W) ≪≫
      Functor.isoWhiskerLeft F (B.flip.mapIso e)

private theorem normalizedTensorIso_app (B : Cat' ⥤ Cat' ⥤ Cat')
    (H F : Cat ⥤ Cat') (J : Cat ⥤ Cat)
    (a : H ≅ J ⋙ F) (b : J ≅ 𝟭 Cat) {W V : Cat'} (e : W ≅ V) (K : Cat) :
    (normalizedTensorIso B H F J a b e).hom.app K =
      ((B.mapIso (a.app K ≪≫ F.mapIso (b.app K))).app W).hom ≫
        ((B.obj (F.obj K)).mapIso e).hom := by
  simp only [normalizedTensorIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_hom_app, Functor.mapIso_hom,
    Iso.app_hom, Functor.flip_obj_map, Functor.flip_map_app]
  exact congrArg (fun f ↦ (B.map (a.hom.app K ≫ f)).app W ≫
    (B.obj (F.obj K)).map e.hom)
      (CategoryTheory.Category.comp_id (F.map (b.hom.app K)))

private theorem remove_identity {A B C D : Cat'} (i i' : A ⟶ B) (f : B ⟶ B)
    (g : B ⟶ C) (h : C ⟶ D) (hf : f = 𝟙 B) (hi : i = i') :
    i ≫ f ≫ g ≫ h = i' ≫ g ≫ h := by
  rw [hf, Category.id_comp, hi]

private theorem cancel_normalizations {A B C D E F G H : Cat'}
    (u : A ⟶ B) (v : C ⟶ D) (w : E ⟶ F) (z : G ⟶ H)
    (iK : A ≅ C) (iL : B ≅ D) (cK : E ≅ G) (cL : F ≅ H)
    (f : C ⟶ E) (g : D ⟶ F)
    (hi : u ≫ iL.hom = iK.hom ≫ v)
    (hc : w ≫ cL.hom = cK.hom ≫ z)
    (hn : u ≫ (iL.hom ≫ g ≫ cL.hom) = (iK.hom ≫ f ≫ cK.hom) ≫ z) :
    v ≫ g = f ≫ w := by
  apply (Iso.cancel_iso_hom_left iK _ _).1
  apply (Iso.cancel_iso_hom_right _ _ cL).1
  simp only [Category.assoc] at hn ⊢
  rw [← reassoc_of% hi, hn, ← hc]

private def firstSourceIso (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) : orderedSource P T 1 ≅ lineSource P T :=
  normalizedTensorIso (tensor (Ring P) (iteratedAffineLine T 1))
    (inverseImage (Ring P) (lastProjection T 0 ≫ 𝟙 T))
    (inverseImage (Ring P) (lastProjection T 0)) (inverseImage (Ring P) (𝟙 T))
    (inverseImageComp (Ring P) (lastProjection T 0) (𝟙 T))
    (inverseImageId (Ring P) T) (lineCoefficientIso P T aT).symm

private theorem firstSourceIso_app (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (K : D P T) :
    (sourceReassociation P T aT K 0).hom = (firstSourceIso P T aT).hom.app K := by
  have h : HEq (sourceReassociation P T aT K 0).hom
      (sourceReassociationRaw P T aT K 0).2.2.hom := by
    unfold sourceReassociation
    exact (sourceReassociation_existsUnique P T aT K 0).exists.choose_spec
  unfold orderedSource lineSource twistAction at h ⊢
  refine (eq_of_heq h).trans ?_
  exact (normalizedTensorIso_app (tensor (Ring P) (iteratedAffineLine T 1))
    (inverseImage (Ring P) (lastProjection T 0 ≫ 𝟙 T))
    (inverseImage (Ring P) (lastProjection T 0)) (inverseImage (Ring P) (𝟙 T))
    (inverseImageComp (Ring P) (lastProjection T 0) (𝟙 T))
    (inverseImageId (Ring P) T) (lineCoefficientIso P T aT).symm K).symm

private theorem firstComposite_natural (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (K L : Plus (Ring P) T) (v : K.obj ⟶ L.obj) :
    (rightDerivedUpperShriek (Ring P) (lastProjection T 0)).map v ≫
        exceptionalComposite P T aT L 0 =
      exceptionalComposite P T aT K 0 ≫ (exceptional P T 1).map v := by
  let : HasCompactification (lastProjection T 0 ≫ 𝟙 (iteratedAffineLine T 0)) :=
    HasCompactification.of_eq (f := lastProjection T 0) (Category.comp_id _).symm
  have he (M : Plus (Ring P) T) : HEq (exceptionalComposite P T aT M 0)
      (exceptionalCompositeRaw P T aT M 0).2.2 := by
    unfold exceptionalComposite
    exact (exceptionalComposite_existsUnique P T aT M 0).exists.choose_spec
  have hK := he K
  have hL := he L
  unfold exceptional at hK hL ⊢
  rw [eq_of_heq hK, eq_of_heq hL]
  exact (rightDerivedUpperShriekCongr (Ring P)
    (Category.comp_id (lastProjection T 0)).symm).hom.naturality v

private theorem comparison_one (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (K : Plus (Ring P) T) (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : etaleFiniteTor (Ring P) T Ke)
    (eK : (comparison (Ring P) T).obj Ke ≅ K.obj) :
    affineSpacePurityComparison P T aT K Ke hKe eK 1 =
      (firstSourceIso P T aT).hom.app K.obj ≫ lineComparison P T aT K Ke hKe eK ≫
        exceptionalComposite P T aT K 0 := by
  unfold affineSpacePurityComparison
  simp only [orderedRec]
  unfold comparisonStep comparisonZero
  change (sourceReassociation P T aT K.obj 0).hom ≫
    (lineSource P T).map (𝟙 K.obj) ≫ lineComparison P T aT K Ke hKe eK ≫
      exceptionalComposite P T aT K 0 = _
  exact remove_identity _ _ _ _ _
    (CategoryTheory.Functor.map_id (lineSource P T) K.obj)
    (firstSourceIso_app P T aT K.obj)

/-- Naturality of one line comparison for an arbitrary arrow between retained finite-Tor
origins. The arrow need not be an isomorphism or an ordered integration transpose.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph; expanded ordered-transpose
proof Step 8 (blueprint: lem-pur-affine-line-comparison-naturality).

Proof: apply orderedAffineComparison_natural at dimension one. The zero comparison is
identity, so its successor is I_0 followed by the line comparison and the exceptional
identity compositor. The inverse-image composition and identity comparisons, whiskered
with the fixed Tate tensor functor and followed by lineCoefficientIso, form firstSourceIso.
Its component is exactly the specified I_0, by sourceReassociation_existsUnique and the
explicit tensorZeroReassociation formula. Thus I_0 is natural in the input. The zero
exceptional compositor is the component of rightDerivedUpperShriekCongr for q followed
by the identity; hence it too is natural and invertible. Rewrite the dimension-one
comparison in the ordered naturality equation, substitute those two naturality squares,
and cancel the source and target isomorphisms. The remaining equation is the displayed
single-line square, for the original retained representatives. The calculation is valid
for arbitrary v, including zero arrows and empty bases. -/
theorem lineComparison_natural (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (K : Plus (Ring P) T) (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (hKe : etaleFiniteTor (Ring P) T Ke)
    (eK : (comparison (Ring P) T).obj Ke ≅ K.obj)
    (L : Plus (Ring P) T) (Le : Etale.DerivedCategoryModule (Ring P) T)
    (hLe : etaleFiniteTor (Ring P) T Le)
    (eL : (comparison (Ring P) T).obj Le ≅ L.obj) (v : K.obj ⟶ L.obj) :
    (lineSource P T).map v ≫ lineComparison P T aT L Le hLe eL =
      lineComparison P T aT K Ke hKe eK ≫
        (rightDerivedUpperShriek (Ring P)
          (AffineSpace PUnit.{u + 1} T ↘ T)).map v := by
  have hn := OrderedAffineTranspose.orderedAffineComparison_natural P T aT
    K Ke hKe eK L Le hLe eL v 1
  have hi := (firstSourceIso P T aT).hom.naturality v
  have hc := firstComposite_natural P T aT K L v
  have hcomp (M : Plus (Ring P) T) : IsIso (exceptionalComposite P T aT M 0) := by
    have he : HEq (exceptionalComposite P T aT M 0)
        (exceptionalCompositeRaw P T aT M 0).2.2 := by
      unfold exceptionalComposite
      exact (exceptionalComposite_existsUnique P T aT M 0).exists.choose_spec
    have he' : exceptionalComposite P T aT M 0 =
        (exceptionalCompositeRaw P T aT M 0).2.2 := by
      unfold exceptional
      exact eq_of_heq he
    rw [he']
    let : HasCompactification (lastProjection T 0 ≫ 𝟙 (iteratedAffineLine T 0)) :=
      HasCompactification.of_eq (f := lastProjection T 0) (Category.comp_id _).symm
    change IsIso ((rightDerivedUpperShriekCongr (Ring P)
      (Category.comp_id (lastProjection T 0)).symm).hom.app M.obj)
    exact NatIso.hom_app_isIso _ _
  let cK := @asIso _ _ _ _ (exceptionalComposite P T aT K 0) (hcomp K)
  let cL := @asIso _ _ _ _ (exceptionalComposite P T aT L 0) (hcomp L)
  have hL := congrArg (fun f ↦ (orderedSource P T 1).map v ≫ f)
    (comparison_one P T aT L Le hLe eL)
  have hK := congrArg (fun f ↦ f ≫ (exceptional P T 1).map v)
    (comparison_one P T aT K Ke hKe eK)
  exact cancel_normalizations _ _ _ _ ((firstSourceIso P T aT).app K.obj)
    ((firstSourceIso P T aT).app L.obj) cK cL
    (lineComparison P T aT K Ke hKe eK) (lineComparison P T aT L Le hLe eL)
    hi hc (hL.symm.trans (hn.trans hK))

end AlgebraicGeometry.ProEtale.AffineSpacePurity
