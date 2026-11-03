/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Pushforward of the zero-section localization triangle

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/`
`lem-pur-gysin-structure.proof.md`, localization paragraph
(blueprint: `lem-pur-gysin-localization-pushforward`).

The terms are the canonical pro-etale ones of `RetractedSupport`, also used by
`lem-pur-gysin-structure`: `closedTerm` is the finite transported exceptional term
`Rs^!K`, `middleTerm` is `Rp_*K`, and `openTerm` is `R(j ≫ p)_* j^*K` after the exact
open pullback, with `K = ν_X^* B` for the etale twist `B = gysinEtaleInput`.  The middle
arrow is `restriction`, the derived image of the open unit followed by the canonical
compositor.  The first arrow and the connecting morphism are fixed by the transport of
the etale-origin localization triangle: `firstComparison` contains the closed counit and
the collapse of `Rp_*Rs_*` along `s ≫ p = 𝟙`, and `thirdComparison` the compositor.
Only the triangle is asserted, not the global support and edge clauses of the full
`RetractedSupport.Comparison` record.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Abelian
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.RetractedSupport

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

private theorem scalarMate_comp
    {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    [Category D₁] [Category D₂] [Category D₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁)
    {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} (a₂ : L₂ ⊣ R₂)
    {M₁ : D₁ ⥤ D₂} {S₁ : D₂ ⥤ D₁} (b₁ : M₁ ⊣ S₁)
    {M₂ : D₂ ⥤ D₃} {S₂ : D₃ ⥤ D₂} (b₂ : M₂ ⊣ S₂)
    {L : C₁ ⥤ C₃} {R : C₃ ⥤ C₁} (a : L ⊣ R)
    {M : D₁ ⥤ D₃} {S : D₃ ⥤ D₁} (b : M ⊣ S)
    {F : C₁ ⥤ D₁} {G : C₂ ⥤ D₂} {H : C₃ ⥤ D₃}
    (α : TwoSquare F L₁ M₁ G) (β : TwoSquare G L₂ M₂ H)
    (γ : TwoSquare F L M H) (u : L ≅ L₁ ⋙ L₂) (v : M ≅ M₁ ⋙ M₂)
    (ho : ∀ K : C₁, M₂.map (α.natTrans.app K) ≫ β.natTrans.app (L₁.obj K) =
      v.inv.app (F.obj K) ≫ γ.natTrans.app K ≫ H.map (u.hom.app K)) (K : C₃) :
    (mateEquiv a₁ b₁ α).natTrans.app (R₂.obj K) ≫
        S₁.map ((mateEquiv a₂ b₂ β).natTrans.app K) ≫
        (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K) =
      F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).hom.app K) ≫
        (mateEquiv a b γ).natTrans.app K := by
  have hs : (TwoSquare.vComp α β).whiskerLeft u.inv = γ.whiskerRight v.inv := by
    ext T
    have ht := congrArg (fun z ↦ z ≫ H.map (u.inv.app T)) (ho T)
    simp only [Category.assoc] at ht
    rw [← H.map_comp, Iso.hom_inv_id_app, H.map_id] at ht
    have htid := congrArg (fun z ↦ v.inv.app (F.obj T) ≫ z)
      (Category.comp_id (γ.natTrans.app T))
    have ht' := ht.trans htid
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using ht'
  have hm := congrArg (mateEquiv a (b₁.comp b₂)) hs
  rw [conjugateEquiv_mateEquiv_vcomp a (a₁.comp a₂) (b₁.comp b₂),
    mateEquiv_conjugateEquiv_vcomp a b (b₁.comp b₂),
    mateEquiv_hcomp a₁ b₁ a₂ b₂] at hm
  have hc := congrArg (fun z ↦ z.natTrans.app K) hm
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at hc
  rw [← conjugateIsoEquiv_apply_inv, ← conjugateIsoEquiv_apply_inv] at hc
  apply (cancel_epi (F.map ((conjugateIsoEquiv (a₁.comp a₂) a u).inv.app K))).mp
  have ht := congrArg
    (fun z ↦ z ≫ (conjugateIsoEquiv (b₁.comp b₂) b v).hom.app (H.obj K)) hc
  simp only [Category.assoc] at ht
  rw [Iso.inv_hom_id_app] at ht
  have ht' := ht.trans (Category.comp_id ((mateEquiv a b γ).natTrans.app K))
  simpa only [Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id_app, F.map_id, Category.id_comp] using ht'


section Restriction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives D] [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]

end Restriction

namespace WeilConjectures.PurityFiniteSetting

set_option maxHeartbeats 2000000 in
-- Normalizing the two derived-functor compatibility isomorphisms requires extra elaboration.
private theorem imageComparison_eq_mate (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus (EtSheaves P X)) :
    imageComparison P p K =
      (mateEquiv
        (Etale.upperStarLowerStarAdjunction (Modules P) p).mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (Modules P) p).mapDerivedCategoryRightDerivedAdjunction
        (unboundedDirectImagePullbackIso P.Coefficient p).hom).app K.obj := by
  let e := (Etale.upperStarLowerStarAdjunction (Modules P) p)
  let d := (upperStarLowerStarAdjunction (Modules P) p)
  apply (d.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  erw [mateEquiv_counit]
  have h := congrArg DerivedCategory.Plus.ι.map
    (fixedComparisonDirectImageMatePlus_counit P.Coefficient p K)
  simp only [Functor.map_comp] at h
  simp only [Etale.derivedUpperStarLowerStarAdjunctionPlus,
    derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus] at h
  change DerivedCategory.Plus.ι.map
      ((fixedComparisonPullbackPlus P.Coefficient p).hom.app
        ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus.obj K)) ≫
    (upperStar (Modules P) p).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus P.Coefficient p).app K)) ≫
    DerivedCategory.Plus.ι.map (d.derivedPlus.counit.app ((nuPlus P X).obj K)) =
      (nu P X).map (DerivedCategory.Plus.ι.map (e.derivedPlus.counit.app K)) at h
  rw [included_counit e K, included_counit d] at h
  rw [included_pullback] at h
  simp only [Functor.map_comp] at h
  have himage : imageComparison P p K =
      (nu P Y).map
        ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus P.Coefficient p).app K) ≫
      (lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((nuPlus P X).obj K) := by
    unfold imageComparison
    dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.app_hom, Iso.app_inv,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    rfl
  rw [himage]
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi ((unboundedDirectImagePullbackIso P.Coefficient p).inv.app
    ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.obj K.obj))).1
  simp only [Iso.inv_hom_id_app_assoc]
  have hn := (unboundedDirectImagePullbackIso P.Coefficient p).inv.naturality
    ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.inv.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  have hh := congrArg (fun t ↦ (nu P X).map
    ((Etale.upperStar (Modules P) p).mapDerivedCategory.map
      ((Etale.lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility.inv.app K)) ≫ t) h
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at hh
  convert hh using 1
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem sfPullback_eq_standard (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) :
    sfDerivedComparisonPullbackIso P.Ring j =
      unboundedDirectImagePullbackIso P.Coefficient j := by
  have hs : sfToProEtBaseChangeIso j = toProEtCompOverPullbackIso j := by
    apply Iso.ext
    apply NatTrans.ext
    funext W
    rfl
  unfold sfDerivedComparisonPullbackIso unboundedDirectImagePullbackIso
    sfComparisonPullbackIso comparisonUpperStarCompUpperStarIso
    sfComparisonDirectImageCompIso lowerStarCompComparisonLowerStarIso
  rw [hs]
  rfl

private theorem pullback_mate_composition (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y)
    (K : DerivedCategory (EtSheaves P Y)) :
    (upperStar (Modules P) j).mapDerivedCategory.map
        ((unboundedDirectImagePullbackIso P.Coefficient p).hom.app K) ≫
      (unboundedDirectImagePullbackIso P.Coefficient j).hom.app
        ((Etale.upperStar (Modules P) p).mapDerivedCategory.obj K) =
    (Functor.mapDerivedCategoryNatIso (upperStarComp (Modules P) j p) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app ((nu P Y).obj K) ≫
      (unboundedDirectImagePullbackIso P.Coefficient (j ≫ p)).hom.app K ≫
      (nu P U).map
        ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (Modules P) j p) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app K) := by
  have hc := Functor.mapDerivedCategorySquareIso_comp
    (Etale.upperStar (Modules P) p) (Etale.upperStar (Modules P) j)
    (Etale.upperStar (Modules P) (j ≫ p))
    (upperStar (Modules P) p) (upperStar (Modules P) j)
    (upperStar (Modules P) (j ≫ p))
    (comparisonUpperStar (Modules P) Y) (comparisonUpperStar (Modules P) X)
    (comparisonUpperStar (Modules P) U)
    (comparisonUpperStarCompUpperStarIso (Modules P) p).symm
    (comparisonUpperStarCompUpperStarIso (Modules P) j).symm
    (comparisonUpperStarCompUpperStarIso (Modules P) (j ≫ p)).symm
    (Etale.upperStarComp (Modules P) j p) (upperStarComp (Modules P) j p)
    (fun F ↦ (comparison_pullback_coherent.2.2 P.Coefficient).2.1 U X Y j p F)
  have hs {V W : Scheme.{u}} (f : V ⟶ W) :
      Functor.mapDerivedCategorySquareIso
        (comparisonUpperStarCompUpperStarIso (Modules P) f).symm =
      (unboundedDirectImagePullbackIso P.Coefficient f).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, unboundedDirectImagePullbackIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  have hi := congrArg (fun e ↦ e.inv.app K) hc
  simp only [hs, Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Iso.symm_inv, Category.assoc] at hi
  apply (cancel_mono ((nu P U).map
    ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (Modules P) j p) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).inv.app K))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  simpa only [Iso.trans_inv, NatTrans.comp_app, nu, Category.assoc] using hi

private noncomputable abbrev imageMate (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    (Etale.upperStarLowerStarAdjunction (Modules P) f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction (Modules P) f).mapDerivedCategoryRightDerivedAdjunction
    (unboundedDirectImagePullbackIso P.Coefficient f).hom).natTrans

private theorem proComp_eq_conjugate (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y) :
    letI := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
    (Functor.rightDerivedFunctorCompIso' (lowerStar (Modules P) j)
      (lowerStar (Modules P) p) (lowerStarComp (Modules P) j p)).hom =
    (conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (Modules P) p).mapDerivedCategoryRightDerivedAdjunction.comp
        (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction)
      (upperStarLowerStarAdjunction (Modules P) (j ≫ p)).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategoryNatIso (upperStarComp (Modules P) j p) ≪≫
        Functor.mapDerivedCategoryCompIso _ _)).hom := by
  let := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  apply Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction (Modules P) j)
    (upperStarLowerStarAdjunction (Modules P) p)
    (upperStarLowerStarAdjunction (Modules P) (j ≫ p))
  have he : conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (Modules P) p).comp
        (upperStarLowerStarAdjunction (Modules P) j))
      (upperStarLowerStarAdjunction (Modules P) (j ≫ p))
      (upperStarComp (Modules P) j p) = lowerStarComp (Modules P) j p := by
    unfold upperStarComp
    rw [conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]
    rfl
  exact (congrArg Iso.hom he).symm

private theorem imageMate_comp (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y)
    (K : DerivedCategory (EtSheaves P U)) :
    letI := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
    (nu P Y).map ((Etale.rightDerivedLowerStarComp (Modules P) j p).hom.app K) ≫
      (imageMate P (j ≫ p)).app K =
    (imageMate P p).app ((Etale.lowerStar (Modules P) j).rightDerivedFunctor.obj K) ≫
      (lowerStar (Modules P) p).rightDerivedFunctor.map ((imageMate P j).app K) ≫
      (Functor.rightDerivedFunctorCompIso' (lowerStar (Modules P) j)
        (lowerStar (Modules P) p) (lowerStarComp (Modules P) j p)).hom.app
        ((nu P U).obj K) := by
  have hm := scalarMate_comp
    (Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) p)
    (Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j)
    (upperStarLowerStarAdjunction (Modules P) p).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction
    (Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) (j ≫ p))
    (upperStarLowerStarAdjunction (Modules P) (j ≫ p)).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (unboundedDirectImagePullbackIso P.Coefficient p).hom)
    (TwoSquare.mk _ _ _ _ (unboundedDirectImagePullbackIso P.Coefficient j).hom)
    (TwoSquare.mk _ _ _ _ (unboundedDirectImagePullbackIso P.Coefficient (j ≫ p)).hom)
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (Modules P) j p) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (Functor.mapDerivedCategoryNatIso (upperStarComp (Modules P) j p) ≪≫
      Functor.mapDerivedCategoryCompIso _ _)
    (pullback_mate_composition P j p) K
  rw [← proComp_eq_conjugate P j p] at hm
  exact hm.symm

private theorem imageComparison_isIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (B : DerivedCategory.Plus (EtSheaves P X)) : IsIso (imageComparison P p B) := by
  have := isIso_comparisonDirectImageCanonicalMate P.Coefficient p
  unfold imageComparison
  infer_instance

private theorem firstComparison_isIso (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    IsIso (firstComparison P p s hs B) := by
  change IsIso ((firstComparisonTransformation P p s hs).app B)
  have := firstComparisonTransformation_isIso P p s hs
  infer_instance

private theorem thirdComparison_isIso (P : PurityFiniteSetting.{u})
    {X Y U : Scheme.{u}} (p : X ⟶ Y) (j : U ⟶ X)
    [QuasiCompact (j ≫ p)] [QuasiSeparated (j ≫ p)]
    (B : DerivedCategory.Plus (EtSheaves P X)) : IsIso (thirdComparison P p j B) := by
  have := imageComparison_isIso P (j ≫ p)
    ((Etale.upperStar (Modules P) j).mapDerivedCategoryPlus.obj B)
  unfold thirdComparison
  infer_instance

private theorem restriction_comparison_square (P : PurityFiniteSetting.{u})
    {U X Y : Scheme.{u}} (j : U ⟶ X) (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (j ≫ p)] [QuasiSeparated (j ≫ p)]
    (B : DerivedCategory.Plus (EtSheaves P X)) :
    (nu P Y).map ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.map
      ((Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j).unit.app B.obj)) ≫
        thirdComparison P p j B =
      imageComparison P p B ≫ (restriction P p j).app B := by
  let := (upperStarLowerStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let R := (lowerStar (Modules P) p).rightDerivedFunctor
  let S := (lowerStar (Modules P) j).rightDerivedFunctor
  let c := Functor.rightDerivedFunctorCompIso' (lowerStar (Modules P) j)
    (lowerStar (Modules P) p) (lowerStarComp (Modules P) j p)
  let K := (Etale.upperStar (Modules P) j).mapDerivedCategory.obj B.obj
  have hc := imageMate_comp P j p K
  have hn := (imageMate P p).naturality
    ((Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j).unit.app B.obj)
  have hu := unit_mateEquiv
    (Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j)
    (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction
    (unboundedDirectImagePullbackIso P.Coefficient j).hom B.obj
  have hu' : (nu P X).map
      ((Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j).unit.app B.obj) ≫
      (imageMate P j).app K ≫
      S.map ((unboundedDirectImagePullbackIso P.Coefficient j).inv.app B.obj) =
    (upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction.unit.app
      ((nu P X).obj B.obj) := by
    erw [reassoc_of% hu]
    erw [← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hum := congrArg R.map hu'
  simp only [Functor.map_comp] at hum
  have hcn := c.hom.naturality
    ((unboundedDirectImagePullbackIso P.Coefficient j).inv.app B.obj)
  dsimp only [Functor.comp_map] at hn hcn
  unfold thirdComparison restriction
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.app_hom, Iso.app_inv,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [imageComparison_eq_mate, imageComparison_eq_mate, sfPullback_eq_standard]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  change (nu P Y).map
      ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction (Modules P) j).unit.app B.obj)) ≫
    (nu P Y).map ((Etale.rightDerivedLowerStarComp (Modules P) j p).hom.app K) ≫
    (imageMate P (j ≫ p)).app K ≫
    (lowerStar (Modules P) (j ≫ p)).rightDerivedFunctor.map
      ((unboundedDirectImagePullbackIso P.Coefficient j).inv.app B.obj) =
    (imageMate P p).app B.obj ≫ R.map
      ((upperStarLowerStarAdjunction (Modules P) j).mapDerivedCategoryRightDerivedAdjunction.unit
        |>.app ((nu P X).obj B.obj)) ≫ c.hom.app _
  rw [reassoc_of% hc, reassoc_of% hn]
  erw [← hcn]
  erw [reassoc_of% hum]
  rfl

set_option maxRecDepth 4096 in
/-- Pushforward of the zero-section localization triangle.

Source: `lem-pur-gysin-structure.proof.md`, the localization paragraph: apply the support
triangle to K and then Rp_* (blueprint: lem-pur-gysin-localization-pushforward).

There are a first arrow `Rs^!K → Rp_*K` and a connecting morphism `Rπ_*j^*K → Rs^!K[1]`
such that, with the middle arrow `restriction`, the triangle is distinguished, and it is
isomorphic to the transport of the distinguished etale localization triangle of
`B = gysinEtaleInput` by the canonical comparisons `firstComparison` (counit and
collapse of `Rp_*Rs_*`), `imageComparison` and `thirdComparison` (compositor).  Since the
comparison is an isomorphism of triangles with these components, the first arrow and the
connecting morphism are determined.

Proof, following the node:
Step 1: the zero section and the basic-open complement have complementary ranges
(`AffineSpace.range_basicOpen_ι_coord`); the etale closed-support localization theorem
(lem-exc-closed-support-triangle) gives a boundary `δet` and the distinguished etale triangle
of `B = gysinEtaleInput`, with the closed counit and the open unit.
Step 2: the right-derived etale direct image along `p` and the comparison pullback `ν_Y` are
triangulated (lem-weil-pbc-derived-direct-image-triangulated), so `transportedTriangle` is
distinguished.
Step 3: `firstComparison` is invertible (collapse along `s ≫ p = 𝟙`, and the comparison unit
is invertible on bounded-below etale objects, thm-weil-pbc-site-comparison);
`imageComparison` and hence `thirdComparison` are invertible by the qcqs direct-image
comparison (lem-weil-pbc-comparison-direct-image-canonical-mate).
Step 4: identifying `imageComparison` with the unbounded adjunction mate and pasting mates
along the pullback-composition coherence proves that the middle square commutes with exactly
`restriction`; conjugating the outer arrows by the three comparisons, `Triangle.isoMk` gives
the triangle isomorphism with the prescribed components, and distinguished triangles are
closed under isomorphism. -/
theorem gysin_localization_pushforward
    (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    ∃ (first : (closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y) ⟶
          (middleTerm P (lineProjection Y)).obj (gysinEtaleInput P h Y))
      (δ : (openTerm P (lineProjection Y) (openImmersion Y)).obj (gysinEtaleInput P h Y) ⟶
          ((closedTerm P (zeroSection Y)).obj (gysinEtaleInput P h Y))⟦(1 : ℤ)⟧)
      (δet : EtaleBoundary P (zeroSection Y) (openImmersion Y)),
      etaleTriangle P (zeroSection Y) (openImmersion Y) δet
          (gysinEtaleInput P h Y).obj ∈ distTriang _ ∧
      Triangle.mk first
          ((restriction P (lineProjection Y) (openImmersion Y)).app (gysinEtaleInput P h Y))
          δ ∈ distTriang (DerivedCategory (ProSheaves P Y)) ∧
      ∃ e : transportedTriangle P (lineProjection Y) (zeroSection Y) (openImmersion Y) δet
            (gysinEtaleInput P h Y) ≅
          Triangle.mk first
            ((restriction P (lineProjection Y) (openImmersion Y)).app (gysinEtaleInput P h Y))
            δ,
        e.hom.hom₁ = firstComparison P (lineProjection Y) (zeroSection Y)
          (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y) (gysinEtaleInput P h Y) ∧
        e.hom.hom₂ = imageComparison P (lineProjection Y) (gysinEtaleInput P h Y) ∧
        e.hom.hom₃ = thirdComparison P (lineProjection Y) (openImmersion Y)
          (gysinEtaleInput P h Y) := by
  classical
  let : IsSeparated (lineProjection Y) := by
    change IsSeparated (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  let : QuasiCompact (lineProjection Y) := by
    change QuasiCompact (AffineSpace (ULift.{u} (Fin 1)) Y ↘ Y)
    infer_instance
  let : QuasiCompact (openImmersion Y) := by
    dsimp [openImmersion, Punctured]
    infer_instance
  have hrange : Set.range (zeroSection Y).base =
      (Set.range (openImmersion Y).base)ᶜ := by
    have hr : Set.range (openImmersion Y).base =
        (Set.range (zeroSection Y).base)ᶜ := by
      simpa [Line, coordinate, openImmersion, Punctured, zeroSection] using
        AffineSpace.range_basicOpen_ι_coord Y
    rw [hr, compl_compl]
  let B := gysinEtaleInput P h Y
  obtain ⟨δet, hδet⟩ := Etale.exists_etale_closedSupportTriangle P.Coefficient
    (zeroSection Y) (openImmersion Y) hrange
  have hT : etaleTriangle P (zeroSection Y) (openImmersion Y) δet B.obj ∈ distTriang _ :=
    hδet B.obj
  let T := transportedTriangle P (lineProjection Y) (zeroSection Y) (openImmersion Y) δet B
  have hTd : T ∈ distTriang _ :=
    (nu P Y).map_distinguished _
      ((Etale.lowerStar (Modules P) (lineProjection Y)).rightDerivedFunctor.map_distinguished
        _ hT)
  have := firstComparison_isIso P (lineProjection Y) (zeroSection Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y) B
  have := imageComparison_isIso P (lineProjection Y) B
  have := thirdComparison_isIso P (lineProjection Y) (openImmersion Y) B
  let e₁ := asIso (firstComparison P (lineProjection Y) (zeroSection Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y) B)
  let e₂ := asIso (imageComparison P (lineProjection Y) B)
  let e₃ := asIso (thirdComparison P (lineProjection Y) (openImmersion Y) B)
  let first := e₁.inv ≫ T.mor₁ ≫ e₂.hom
  let δ := e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧'
  have hmid : T.mor₂ ≫ e₃.hom =
      e₂.hom ≫ (restriction P (lineProjection Y) (openImmersion Y)).app B :=
    restriction_comparison_square P (openImmersion Y) (lineProjection Y) B
  let e : T ≅ Triangle.mk first
      ((restriction P (lineProjection Y) (openImmersion Y)).app B) δ :=
    Triangle.isoMk _ _ e₁ e₂ e₃
      (by simp only [Triangle.mk_mor₁, first, Iso.hom_inv_id_assoc])
      hmid
      (by simp only [Triangle.mk_mor₃, δ, Iso.hom_inv_id_assoc])
  refine ⟨first, δ, δet, hT, ?_, e, ?_, ?_, ?_⟩
  · exact isomorphic_distinguished T hTd _ e.symm
  · rfl
  · rfl
  · rfl

end WeilConjectures.PurityFiniteSetting
