/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSuccessorClosedComposition
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.ClosedProperOriginComposition
import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateExactDerivedCompositionSingle

/-! # The closed-single normalization of the specified origin compositor

Source: exact closed comparisons and compact-support composition in the current
blueprint's affine-space zero-section proof.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
-- Match the sheaf abelian data used by the compact-support definitions.
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

private theorem normalizationClosedSingle (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    closedSingleIso A i M =
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) i).app ((DerivedCategory.singleFunctor _ 0).obj M) ≪≫
      (lowerStar (ModuleCat.{u + 1} A) i).singleFunctorCompRightDerivedFunctorIso.app M := by
  rfl

private theorem paste_single_comparison
    {D E : Type*} [Category* D] [Category* E]
    (G G' : D ⥤ E) (eG : G ≅ G') {M M' N : D} {X Q T P : E}
    (c : X ⟶ G.obj M) (eF : M ≅ M') (eH : X ≅ Q)
    (d : Q ⟶ G'.obj M') (sF : M' ≅ N) (sG : G'.obj N ≅ P)
    (sH : Q ≅ T) (t : T ⟶ P)
    (hp : c ≫ G.map eF.hom ≫ eG.hom.app M' = eH.hom ≫ d)
    (hs : d ≫ G'.map sF.hom ≫ sG.hom = sH.hom ≫ t) :
    c ≫ G.map (eF ≪≫ sF).hom =
      (eH ≪≫ sH).hom ≫ t ≫ (eG.app N ≪≫ sG).inv := by
  apply (cancel_mono (eG.app N ≪≫ sG).hom).1
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id, Category.comp_id]
  calc
    _ = (c ≫ G.map eF.hom ≫ eG.hom.app M') ≫ G'.map sF.hom ≫ sG.hom := by
      simp only [Category.assoc, eG.hom.naturality_assoc]
    _ = _ := by
      rw [hp]
      simpa only [Category.assoc] using congrArg (fun z ↦ eH.hom ≫ z) hs

-- These definitions express the same last section and successor scheme.
attribute [local implicit_reducible] iteratedAffineLine zero
  Scheme.Hom.toIteratedAffineLine AffineSpace.zeroSection

private theorem normalizationLastExact
    (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (lastSection B r)) := by
  let := AffineSpacePurity.tower_noetherian (setting P n) B aB (r + 1)
  exact preservesFiniteColimits_lowerStar_of_isCompl (lastSection B r)
    (lastSection B r).openComplement.ι
    (eq_compl_iff_isCompl.mp (lastSection B r).range_eq_compl_range_openComplement_ι)

set_option cleanup.letToHave false in
set_option maxHeartbeats 1500000 in
-- Pasting the concrete derived-category comparisons requires extra kernel reductions.
/-- The specified compact-support compositor has the ordinary closed-single
normalization at the constant coefficient. There is no tensor or supported class.
Source: the compact-support composition step of the zero-section argument.
(blueprint: lem-pur-coordinate-successor-closed-composition-normalization).

Proof: apply the fully faithful etale-origin comparison to the equation. The
ambient compositor becomes its defining etale model. Expand each proper
closed-single comparison as the open-to-direct-image comparison, the
right-derived composition comparison and the exact-single comparison. The
counit-defined proper site comparison commutes with ordinary direct-image
composition: transpose both sides under inverse image and direct image, then
apply counit naturality and the compositor law for inverse image. The chosen
compactifications are compared through common refinements; their open units
and proper counits cancel in these mate squares. The etale compositor therefore
becomes the ordinary right-derived lowerStar compositor. Exactness identifies
this with mapDerivedCategoryCompIso. The canonical single-functor composition
law then leaves lowerStarComp on constant coefficients. Finally transport the
zero_successor equality through lowerStarCongr. This is precisely the concrete
successorClosedComposition. Faithfulness gives the asserted original equality. -/
theorem coordinate_successor_closed_composition_normalization
    (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB] (r : ℕ) :
    let := zero_exact P n B aB r
    (coordinateComposition P n B r).hom ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
        (lastSection B r)).map
        (closedSingleIso (setting P n).Coefficient (zero B r)
          ((setting P n).constant B)).hom =
      successorClosedComposition P n B aB r := by
  let := zero_exact P n B aB r
  let := zero_exact P n B aB (r + 1)
  let := normalizationLastExact P n B aB r
  let A := (setting P n).Coefficient
  let f := zero B r
  let g := lastSection B r
  let h := zero B (r + 1)
  let q : h = f ≫ g := (CoordinateTowerNormalization.zero_successor B r).symm
  let M := (setting P n).constant B
  let F := lowerStar (ModuleCat.{u + 1} A) f
  let G := lowerStar (ModuleCat.{u + 1} A) g
  let H := lowerStar (ModuleCat.{u + 1} A) h
  let : F.PreservesKInjectiveComplexes :=
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).preservesKInjectiveComplexes
  let e : H ≅ F ⋙ G := lowerStarCongr (ModuleCat.{u + 1} A) q ≪≫
    (lowerStarComp (ModuleCat.{u + 1} A) f g).symm
  let K := unit P n B
  let Rg := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
  let c := (coordinateComposition P n B r).hom
  let ef := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f
  let eg := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) g
  let eh := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) h
  let sf := F.rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app M
  let sg := G.rightDerivedFunctorIsoMapDerivedCategory.app
      ((DerivedCategory.singleFunctor _ 0).obj (F.obj M)) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (F.obj M)
  let sh := H.rightDerivedFunctorIsoMapDerivedCategory.app K ≪≫
    (H.mapDerivedCategorySingleFunctor 0).app M
  let d := ((Functor.rightDerivedFunctorNatIso e) ≪≫
    Functor.rightDerivedFunctorCompIso F G).hom.app K
  have hp := coordinate_closed_proper_origin_composition P n B r
  have hs := coordinate_exact_derived_composition_single P n B r
  have hp' : c ≫ Rg.map (ef.hom.app K) ≫ eg.hom.app (F.rightDerivedFunctor.obj K) =
      eh.hom.app K ≫ d := by
    simpa only [c, d, e, F, G, H, Rg, ef, eg, eh,
      A, f, g, h, q, K,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.comp_obj,
      ObjectProperty.ι_obj, Category.assoc] using hp
  have hs' : d ≫ G.rightDerivedFunctor.map sf.hom ≫ sg.hom =
      sh.hom ≫ (DerivedCategory.singleFunctor _ 0).map (e.hom.app M) := by
    simpa only [d, sf, sg, sh, K, A, f, g, h, q, F, G, H, e, M,
      Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.assoc] using hs
  have result := paste_single_comparison Rg G.rightDerivedFunctor eg c (ef.app K) (eh.app K)
    d sf sg sh ((DerivedCategory.singleFunctor _ 0).map (e.hom.app M)) hp' hs'
  have hf : (ef.app K ≪≫ sf) = closedSingleIso A f M :=
    (normalizationClosedSingle A f M).symm
  have hg : (eg.app ((DerivedCategory.singleFunctor _ 0).obj (F.obj M)) ≪≫ sg) =
      closedSingleIso A g (F.obj M) :=
    (normalizationClosedSingle A g (F.obj M)).symm
  have hh : (eh.app K ≪≫ sh) = closedSingleIso A h M :=
    (normalizationClosedSingle A h M).symm
  erw [hf, hg, hh] at result
  unfold successorClosedComposition
  exact result

end AlgebraicGeometry.ProEtale.AffineZeroPurity
