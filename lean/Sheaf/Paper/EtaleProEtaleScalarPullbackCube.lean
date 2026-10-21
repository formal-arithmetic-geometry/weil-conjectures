/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.EtaleProEtaleScalarMate
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import all Sheaf.Paper.EtaleProEtaleScalarMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The etale/pro-etale scalar and inverse-image cube

Source: Stacks Project, Cohomology on Sites, Tag 0D6D,
`lemma-derived-pullback-composition`, with Tags 06YS, 0G7E, 06YY and 07A4;
Modules on Sites, Tags 03EK and 03EL.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private abbrev adjLeft {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (_a : L ⊣ R) := L

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (upperStar (ModuleCat.{u + 1} A) f).map ((pbcComparisonRestrict Y a).inv.app N) ≫
      (upperStarRestrictScalarsIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).obj N) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology X) a).map
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f).hom.app N) =
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).map
        ((Etale.upperStarRestrictScalarsIsoSheaf a f).hom.app N) ≫
      (pbcComparisonRestrict X a).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) f).obj N) := by
  let cyA := comparisonAdjunction (ModuleCat.{u + 1} A) Y
  let cxA := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let cyB := comparisonAdjunction (ModuleCat.{u + 1} B) Y
  let cxB := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let pA := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let pB := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let lA := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let lB := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let ey := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology a
  let ex := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology a
  let py := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a
  let px := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a
  let e₁ := Functor.isoWhiskerRight (pbcComparisonRestrict Y a).symm (adjLeft pA)
  let e₂ := Functor.associator (adjLeft cyB) (adjLeft py) (adjLeft pA)
  let e₃ := Functor.isoWhiskerLeft (adjLeft cyB) (upperStarRestrictScalarsIso a f)
  let e₄ := (Functor.associator (adjLeft cyB) (adjLeft pB) (adjLeft px)).symm
  let e₅ := Functor.isoWhiskerRight
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f) (adjLeft px)
  let e₁' := Functor.associator (adjLeft ey) (adjLeft cyA) (adjLeft pA)
  let e₂' := Functor.isoWhiskerLeft (adjLeft ey)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)
  let e₃' := (Functor.associator (adjLeft ey) (adjLeft lA) (adjLeft cxA)).symm
  let e₄' := Functor.isoWhiskerRight (Etale.upperStarRestrictScalarsIsoSheaf a f) (adjLeft cxA)
  let e₅' := Functor.associator (adjLeft lB) (adjLeft ex) (adjLeft cxA)
  let e₆' := Functor.isoWhiskerLeft (adjLeft lB) (pbcComparisonRestrict X a).symm
  let e₇' := (Functor.associator (adjLeft lB) (adjLeft cxB) (adjLeft px)).symm
  have h : (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e₄) ≪≫ e₅ =
      (((((e₁' ≪≫ e₂') ≪≫ e₃') ≪≫ e₄') ≪≫ e₅') ≪≫ e₆') ≪≫ e₇' := by
    apply (conjugateIsoEquiv ((lB.comp cxB).comp px) ((ey.comp cyA).comp pA)).injective
    rw [conjugateIsoEquiv_trans _ ((cyB.comp pB).comp px),
      conjugateIsoEquiv_trans _ (cyB.comp (pB.comp px)),
      conjugateIsoEquiv_trans _ (cyB.comp (py.comp pA)),
      conjugateIsoEquiv_trans _ ((cyB.comp py).comp pA)]
    rw [conjugateIsoEquiv_trans _ (lB.comp (cxB.comp px)),
      conjugateIsoEquiv_trans _ (lB.comp (ex.comp cxA)),
      conjugateIsoEquiv_trans _ ((lB.comp ex).comp cxA),
      conjugateIsoEquiv_trans _ ((ey.comp lA).comp cxA),
      conjugateIsoEquiv_trans _ (ey.comp (lA.comp cxA)),
      conjugateIsoEquiv_trans _ (ey.comp (cyA.comp pA))]
    dsimp only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇']
    simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_isoWhiskerLeft]
    simp only [cyA, cxA, cyB, cxB, pA, pB, lA, lB, ey, ex, py, px,
      pbcComparisonRestrict, comparisonUpperStarCompUpperStarIso,
      upperStarRestrictScalarsIso, Etale.upperStarRestrictScalarsIsoSheaf,
      Adjunction.leftAdjointUniq, conjugateIsoEquiv_iso_symm,
      Equiv.apply_symm_apply, conjugateIsoEquiv_associator]
    erw [Equiv.apply_symm_apply]
    ext F V x
    simp only [lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    simp
    rfl
  simpa only [e₁, e₂, e₃, e₄, e₅, e₁', e₂', e₃', e₄', e₅', e₆', e₇',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, pA, px, cyB, ey, cxA, lB] using
    congrArg (fun e ↦ e.hom.app N) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict Y a).inv.app N) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a).map
        ((Functor.mapDerivedCategorySquareIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f)).hom.app N) =
    (Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f)).hom.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom.app N) ≫
      (pbcDerivedComparisonRestrict X a).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory.obj N) := by
  let r₀ := Sheaf.restrictScalars Y.smallEtaleTopology a
  let r₁ := Sheaf.restrictScalars (Scheme.ProEt.topology Y) a
  let r₂ := Sheaf.restrictScalars (Scheme.ProEt.topology X) a
  let cA := comparisonUpperStar (ModuleCat.{u + 1} A) Y
  let cB := comparisonUpperStar (ModuleCat.{u + 1} B) Y
  let pA := upperStar (ModuleCat.{u + 1} A) f
  let pB := upperStar (ModuleCat.{u + 1} B) f
  let dA := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f
  let dB := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} B) f
  let α : r₀ ⋙ (cA ⋙ pA) ≅ (cB ⋙ pB) ⋙ r₂ :=
    (Functor.associator r₀ cA pA).symm ≪≫
      Functor.isoWhiskerRight (pbcComparisonRestrict Y a).symm pA ≪≫
      Functor.associator cB r₁ pA ≪≫
      Functor.isoWhiskerLeft cB (upperStarRestrictScalarsIso a f) ≪≫
      (Functor.associator cB pB r₂).symm
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (pbcComparisonRestrict Y a).symm (upperStarRestrictScalarsIso a f) α
    (Iso.refl (cA ⋙ pA)) (Iso.refl (cB ⋙ pB)) (fun K ↦ by
      simp only [α, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app]
      dsimp only [cA, cB, pA, pB, r₀, r₁, r₂, Functor.comp_obj]
      simp) N
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (Etale.upperStarRestrictScalarsIsoSheaf a f) (pbcComparisonRestrict X a).symm α
    dA dB (fun K ↦ by
      simpa only [α, cA, cB, pA, pB, r₀, r₁, r₂, dA, dB,
        Functor.comp_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Category.id_comp, Category.comp_id, Category.assoc] using
        ordinary_restriction_cube a f K) N
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.mapDerivedCategoryNatIso_refl, Category.id_comp] at h₁
  have htdA : (Functor.mapDerivedCategoryTriangleIso dA).hom =
      (Functor.mapDerivedCategoryCompIso cA pA).hom ≫
        (Functor.mapDerivedCategorySquareIso dA).hom := by
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso]
  have htdB : (Functor.mapDerivedCategoryTriangleIso dB).hom =
      (Functor.mapDerivedCategoryCompIso cB pB).hom ≫
        (Functor.mapDerivedCategorySquareIso dB).hom := by
    simp [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryTriangleIso]
  erw [htdA, htdB] at h₂
  simp only [NatTrans.comp_app, Functor.map_comp, ← Category.assoc] at h₂
  erw [h₁] at h₂
  have h := (cancel_epi ((Functor.mapDerivedCategoryCompIso cA pA).hom.app
    (r₀.mapDerivedCategory.obj N))).1 (by simpa only [Category.assoc] using h₂)
  simpa only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, NatTrans.comp_app,
    pbcDerivedComparisonRestrict, Iso.symm_inv, Sheaf.derivedRestrictScalars,
    Category.assoc, cA, pA, cB, pB, dA, dB, r₀, r₂] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    L(upperStar (ModuleCat.{u + 1} A) f).map
        ((pbcDerivedComparisonRestrict Y a).inv.app N) ≫
      (leftDerivedUpperStarRestrictScalarsIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso B f).hom.app N) =
    (directImageComparisonAmbientPullbackIso A f).hom.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).obj N) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.scalarRestrictionPullbackIso a f).hom.app N) ≫
      (pbcDerivedComparisonRestrict X a).inv.app
        (L(Etale.upperStar (ModuleCat.{u + 1} B) f).obj N) := by
  unfold leftDerivedUpperStarRestrictScalarsIso directImageComparisonAmbientPullbackIso
    Etale.scalarRestrictionPullbackIso
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.naturality_assoc]
  erw [(pbcDerivedComparisonRestrict X a).inv.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [Functor.map_comp, Category.assoc]
  have h := exact_restriction_cube a f N
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] at h
  erw [reassoc_of% h]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_whiskerTop
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reverse_scalar_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (scalarPullbackReverseProEtale a f).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫
      L(upperStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction Y a).hom.app M) ≫
      (directImageComparisonAmbientPullbackIso B f).hom.app
        ((pbcFixedScalarExtension Y.smallEtaleTopology a).obj M) =
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso A f).hom.app M) ≫
      (pbcComparisonReduction X a).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((scalarPullbackReverseEtale a f).app M) := by
  let a₀ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  let a₁ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) a)
  let a₁' := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology a)
  let a₂ := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a)
  let sy := (mateEquiv a₀ a₁).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict Y a).inv)
  let sp := (mateEquiv a₁ a₂).symm
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)
  let se := (mateEquiv a₀ a₁').symm
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)
  let sx := (mateEquiv a₁' a₂).symm
    (TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict X a).inv)
  have h : (TwoSquare.hComp sy sp).whiskerBottom
        (directImageComparisonAmbientPullbackIso B f).hom =
      (TwoSquare.hComp se sx).whiskerTop (directImageComparisonAmbientPullbackIso A f).hom := by
    apply (mateEquiv a₀ a₂).injective
    rw [mateEquiv_whiskerBottom, mate_whiskerTop,
      mateEquiv_vcomp a₀ a₁ a₂, mateEquiv_vcomp a₀ a₁' a₂]
    dsimp only [sy, sp, se, sx]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    ext N
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using derived_restriction_cube a f N
  simpa only [sy, sp, se, sx, a₀, a₁, a₁', a₂,
    TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    pbcComparisonReduction, asIso_hom, pbcComparisonReductionMap, pbcFixedScalarExtension,
    scalarPullbackReverseProEtale, scalarPullbackReverseEtale,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun t ↦ t.natTrans.app M) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical inverse-image square commutes with derived scalar extension.
Source: Stacks Project, Tag 0D6D, `lemma-derived-pullback-composition`.
(blueprint: lem-sfb-etale-proetale-scalar-pullback-cube).

Proof:
1. The ordinary inverse-image square of sk-thm-pe-direct-image-comparison is the
   lift of one geometric square to modules over each constant ring. Naturality
   for addition, scalar multiplication and constant sections identifies its ring
   components with the canonical constant-ring pullbacks, compatibly with a.
2. Apply that naturality to the universal balanced pairing B times N into
   B tensor_A N. Naturality for both product projections identifies the action on
   the product with the product of the two actions. Both ordinary cube paths
   therefore take b tensor m to b tensor theta(m). The balancing relation is
   preserved. The pure-tensor normalization of
   def-weil-pbc-canonical-ringed-tensor-comparison and
   lem-weil-pbc-canonical-ringed-tensor-comparison-construction, followed by module
   sheafification, proves equality on all generalized sections.
3. Resolve an arbitrary representative of M by a K-flat complex P with flat
   terms (lem-pc-kflat-resolution). Ringed pullback preserves this class
   (lem-weil-pbc-ringed-topoi-derived-tensor-pullback), including pullback along
   the identity geometric morphism with structural ring map a. Thus all iterated
   derived functors are computed by ordinary pullbacks of this same P, using
   lem-weil-pbc-ringed-topoi-derived-pullback and lem-pur-derived-change-of-rings.
4. The defining normalization of def-pur-etale-scalar-pullback-iso and the
   composition and specified-2-isomorphism normalization of
   lem-sfb-ringed-derived-monoidal-comparisons identify each scalar face with its
   ordinary face on P. The two d faces are the exact localization of the ordinary
   site square. Localizing the degreewise equality from step 2 proves the cube
   at Q(P). The coefficient is in degree zero, so no factors or signs are swapped.
5. Both paths are natural in M. Transport their equality along the resolution
   isomorphism Q(P) isomorphic to M to obtain the displayed equation. No
   finiteness of f, boundedness of M, or flatness of a is used. -/
theorem etaleProEtale_scalar_pullback_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (scalarPullbackProEtaleIso a f).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology X) a).map
        ((directImageComparisonAmbientPullbackIso A f).hom.app M) ≫
      (pbcComparisonReduction X a).hom.app
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj M) =
    L(upperStar (ModuleCat.{u + 1} B) f).map
        ((pbcComparisonReduction Y a).hom.app M) ≫
      (directImageComparisonAmbientPullbackIso B f).hom.app
        ((pbcFixedScalarExtension Y.smallEtaleTopology a).obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.scalarPullbackIso a f).hom.app M)  := by
  have h := reverse_scalar_cube a f M
  have hp := (scalarPullbackReverse_isIso a f).1
  have he := (scalarPullbackReverse_isIso a f).2
  have h' := congrArg (fun z ↦
    (scalarPullbackProEtaleIso a f).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj M) ≫ z ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
          ((scalarPullbackEtaleIsoFromMate a f).hom.app M)) h
  simp only [scalarPullbackProEtaleIso, scalarPullbackEtaleIsoFromMate,
    Iso.symm_hom, Category.assoc, ← Functor.map_comp,
    asIso_inv, NatIso.isIso_inv_app, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id] at h'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h'
  have hnorm : Etale.scalarPullbackIso a f = scalarPullbackEtaleIsoFromMate a f :=
    scalarPullbackEtaleIso_eq_fromMate a f
  rw [hnorm]
  simpa only [scalarPullbackProEtaleIso, scalarPullbackEtaleIsoFromMate,
    Iso.symm_hom, asIso_inv, NatIso.isIso_inv_app] using h'.symm

end AlgebraicGeometry.ProEtale
