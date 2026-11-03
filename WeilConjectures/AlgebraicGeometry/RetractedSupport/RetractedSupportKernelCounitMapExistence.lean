/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.SupportedHomAdjunctionClass
public import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSupportSequence
public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportGlobalComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.CategoryTheory.UnboundedSectionsLocalization.UnboundedSectionsLocalization

/-! The canonical support kernel map and its forget-support square.
Source: the injective-kernel and derived-unit construction in
`lem-pur-gysin-structure.proof.md` (blueprint: lem-pur-retracted-support-kernel-counit-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.ProEtale.RetractedSupport

private def firstSource (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :=
  DerivedCategory.Plus.ι ⋙ etClosed P s ⋙
    (Etale.lowerStar (Modules P) s).rightDerivedFunctor ⋙
    (Etale.lowerStar (Modules P) p).rightDerivedFunctor ⋙ nu P Y

private def firstComparisonNat (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 Y) : firstSource P p s ⟶ closedTerm P s :=
  firstComparisonTransformation P p s hs

private theorem firstComparisonNat_app (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 Y) (B : DerivedCategory.Plus (EtSheaves P X)) :
    (firstComparisonNat P p s hs).app B = firstComparison P p s hs B :=
  firstComparisonTransformation_app P p s hs B

private def closedKernelIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :
    Etale.closedUpperShriek (Modules P) s s.openComplement.ι ⋙
        Etale.sectionsFunctor (Modules P) Y ≅ etaleSupportKernel P.Coefficient s :=
  Functor.isoWhiskerLeft _ (supportEtaleGlobalEvaluationIso P.Coefficient Y).symm ≪≫
    Etale.normalization_closedUpperShriekCompΓIso (Modules P) s ≪≫
    supportKernelEvaluationIso P.Coefficient s

private theorem closedKernelIso_forget (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] (F : EtSheaves P X) :
    (etImageSectionsIso P s).hom.app
        ((Etale.closedUpperShriek (Modules P) s s.openComplement.ι).obj F) ≫
      (closedKernelIso P s).hom.app F ≫
        (Sheaf.supportedSectionsInclusion X.smallEtaleTopology (Modules P)
          (Etale.supportRestrictionArrow s)).app F =
      (Etale.sectionsFunctor (Modules P) X).map
        ((Etale.lowerStarClosedUpperShriekAdjunction (Modules P) s s.openComplement.ι
          s.range_eq_compl_range_openComplement_ι).counit.app F) := by
  have hk := NatTrans.congr_app
    (supportKernelEvaluationIso_existsUnique P.Coefficient s).choose_spec.1 F
  simp only [NatTrans.comp_app] at hk
  dsimp only [closedKernelIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  simp only [Category.assoc]
  erw [hk]
  erw [reassoc_of%
    Etale.normalization_closedUpperShriekCompΓIso_hom_comp (Modules P) s F]
  erw [reassoc_of% etImageSectionsIso_global P s
    ((Etale.closedUpperShriek (Modules P) s s.openComplement.ι).obj F)]
  simp only [Iso.hom_inv_id_app_assoc]
  erw [(supportEtaleGlobalEvaluationIso P.Coefficient X).hom.naturality]
  erw [Iso.inv_hom_id_app_assoc]

private theorem chosenClosedKernelIso_exists (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :
    ∃ e : etClosed P s ⋙ (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor ≅
        (etaleSupportKernel P.Coefficient s).rightDerivedFunctor,
      Functor.whiskerLeft (etClosed P s) (etImageGlobalIso P s).hom ≫ e.hom ≫
        Functor.rightDerivedFunctorNatTrans
          (Sheaf.supportedSectionsInclusion X.smallEtaleTopology (Modules P)
            (Etale.supportRestrictionArrow s)) =
      Functor.whiskerRight
        (Adjunction.ofIsLeftAdjoint (Etale.lowerStar (Modules P) s).rightDerivedFunctor).counit
        (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor := by
  let L := Etale.lowerStar (Modules P) s
  let R := Etale.closedUpperShriek (Modules P) s s.openComplement.ι
  let a := Etale.lowerStarClosedUpperShriekAdjunction (Modules P) s s.openComplement.ι
    s.range_eq_compl_range_openComplement_ι
  let ad := a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoLeft
    L.rightDerivedFunctorIsoMapDerivedCategory.symm
  let ac := Adjunction.ofIsLeftAdjoint L.rightDerivedFunctor
  let := a.preservesKInjectiveComplexes
  let := (Etale.upperStarLowerStarAdjunction (Modules P) s).preservesKInjectiveComplexes
  let d := Functor.rightDerivedFunctorCompIso' R
    (Etale.sectionsFunctor (Modules P) Y) (closedKernelIso P s)
  let r := ac.rightAdjointUniq ad
  have hd := derivedKernelCounit L R (Etale.sectionsFunctor (Modules P) X)
    (Etale.sectionsFunctor (Modules P) Y) (etaleSupportKernel P.Coefficient s)
    a (etImageSectionsIso P s) (closedKernelIso P s)
    (Sheaf.supportedSectionsInclusion X.smallEtaleTopology (Modules P)
      (Etale.supportRestrictionArrow s)) (closedKernelIso_forget P s)
  refine ⟨Functor.isoWhiskerRight r _ ≪≫ d, ?_⟩
  apply NatTrans.ext
  funext B
  have hB := NatTrans.congr_app hd B
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hB
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app,
    Functor.isoWhiskerRight_hom, Category.assoc]
  erw [← (etImageGlobalIso P s).hom.naturality_assoc, hB,
    ← (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor.map_comp,
    Adjunction.rightAdjointUniq_hom_app_counit ac ad B]

private def etaleFirstSource (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :=
  DerivedCategory.Plus.ι ⋙ etClosed P s ⋙
    (Etale.lowerStar (Modules P) s).rightDerivedFunctor ⋙
    (Etale.lowerStar (Modules P) p).rightDerivedFunctor

private def closedPlus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :=
  (Etale.closedUpperShriek (Modules P) s s.openComplement.ι).rightDerivedFunctorPlus

private def closedPlusCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :
    closedPlus P s ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ etClosed P s :=
  (Etale.closedUpperShriek (Modules P) s s.openComplement.ι).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      ((Etale.derivedLowerStarClosedUpperShriekAdjunction (R := P.Coefficient) s
          s.openComplement.ι s.range_eq_compl_range_openComplement_ι).rightAdjointUniq
        (Adjunction.ofIsLeftAdjoint (Etale.lowerStar (Modules P) s).rightDerivedFunctor))

private def firstSourcePlus (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :=
  closedPlus P s ⋙ (Etale.lowerStar (Modules P) s).rightDerivedFunctorPlus ⋙
    (Etale.lowerStar (Modules P) p).rightDerivedFunctorPlus

private def firstSourcePlusCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :
    firstSourcePlus P p s ⋙ DerivedCategory.Plus.ι ≅ etaleFirstSource P p s :=
  Functor.isoWhiskerLeft
      (closedPlus P s ⋙ (Etale.lowerStar (Modules P) s).rightDerivedFunctorPlus)
      (Etale.lowerStar (Modules P) p).rightDerivedFunctorPlusCompatibility ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (closedPlus P s)
        (Etale.lowerStar (Modules P) s).rightDerivedFunctorPlusCompatibility)
      (Etale.lowerStar (Modules P) p).rightDerivedFunctor ≪≫
    Functor.isoWhiskerRight (closedPlusCompatibility P s)
      ((Etale.lowerStar (Modules P) s).rightDerivedFunctor ⋙
        (Etale.lowerStar (Modules P) p).rightDerivedFunctor)

private def globalUnitDerived (P : WeilConjectures.PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    (Etale.sectionsFunctor (Modules P) X).rightDerivedFunctor ⟶
      nu P X ⋙ global P X :=
  Functor.rightDerivedPullback (comparisonUpperStar (Modules P) X)
    (finiteComparisonGlobalSectionsUnit X P.Coefficient)

private def sourceEtaleIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :
    firstSource P p s ⋙ global P Y ≅
      etaleFirstSource P p s ⋙ (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor :=
  Functor.isoWhiskerRight (firstSourcePlusCompatibility P p s).symm
      (nu P Y ⋙ global P Y) ≪≫
    Functor.isoWhiskerLeft (firstSourcePlus P p s) (globalComparisonIso P Y).symm ≪≫
    Functor.isoWhiskerRight (firstSourcePlusCompatibility P p s)
      (Etale.sectionsFunctor (Modules P) Y).rightDerivedFunctor

private theorem sourceEtaleIso_inverse (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :
    (sourceEtaleIso P p s).hom ≫
      Functor.whiskerLeft (etaleFirstSource P p s) (globalUnitDerived P Y) = 𝟙 _ := by
  apply NatTrans.ext
  funext B
  simp only [sourceEtaleIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Category.assoc]
  erw [(globalUnitDerived P Y).naturality]
  erw [← globalComparisonIso_hom P Y ((firstSourcePlus P p s).obj B)]
  simp only [Iso.inv_hom_id_app_assoc, Functor.comp_map, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rfl

private theorem supportUnitDerived_forget (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s] :
    Functor.rightDerivedPullback (comparisonUpperStar (Modules P) X)
        (supportComparisonUnit P.Coefficient s) ≫
      Functor.whiskerLeft (nu P X) (Functor.rightDerivedFunctorNatTrans
        (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s))) =
    Functor.rightDerivedFunctorNatTrans
        (Sheaf.supportedSectionsInclusion X.smallEtaleTopology (Modules P)
          (Etale.supportRestrictionArrow s)) ≫ globalComparisonDerived P X := by
  symm
  apply Functor.rightDerivedFunctorNatTrans_comp_rightDerivedPullback
  apply NatTrans.ext
  funext F
  exact ((supportComparisonUnit_existsUnique P.Coefficient s).choose_spec.1 F).symm

private theorem sourceSupportMap_exists (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] :
    ∃ k : firstSource P p s ⋙ global P Y ⟶ input P X ⋙
        (supportSections s P.Coefficient).rightDerivedFunctor,
      ∀ B : DerivedCategory.Plus (EtSheaves P X),
        k.app B ≫ (Functor.rightDerivedFunctorNatTrans
          (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
            (supportRestrictionArrow s))).app ((input P X).obj B) =
        (global P Y).map ((nu P Y).map
          ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.map
            ((Adjunction.ofIsLeftAdjoint
              (Etale.lowerStar (Modules P) s).rightDerivedFunctor).counit.app B.obj)) ≫
            imageComparison P p B) ≫
          (imageGlobalIso P p).hom.app ((input P X).obj B) := by
  obtain ⟨e, he⟩ := chosenClosedKernelIso_exists P s
  let k := (sourceEtaleIso P p s).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ etClosed P s ⋙
      (Etale.lowerStar (Modules P) s).rightDerivedFunctor) (etImageGlobalIso P p).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ etClosed P s)
      (etImageGlobalIso P s).hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.ι e.hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.ι
      (Functor.rightDerivedPullback (comparisonUpperStar (Modules P) X)
        (supportComparisonUnit P.Coefficient s))
  refine ⟨k, fun B ↦ ?_⟩
  have hs := NatTrans.congr_app (supportUnitDerived_forget P s) B.obj
  have hc := NatTrans.congr_app he B.obj
  have hi := NatTrans.congr_app (sourceEtaleIso_inverse P p s) B
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hs hc hi
  dsimp only [k, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  simp only [Category.assoc]
  erw [hs, reassoc_of% hc]
  erw [← (etImageGlobalIso P p).hom.naturality_assoc]
  erw [(globalComparison_transport P p B).symm]
  let f := (Etale.lowerStar (Modules P) p).rightDerivedFunctor.map
    ((Adjunction.ofIsLeftAdjoint
      (Etale.lowerStar (Modules P) s).rightDerivedFunctor).counit.app B.obj)
  erw [(globalComparisonDerived P Y).naturality_assoc f]
  change _ ≫ (globalUnitDerived P Y).app ((etaleFirstSource P p s).obj B) ≫ _ = _
  erw [reassoc_of% hi]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem sourceSupportHyperMap_exists (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X) [IsClosedImmersion s] (q : ℤ) :
    ∃ k : firstSource P p s ⋙ hyper P Y q ⟶ nuPlus P X ⋙
        Sheaf.supportHypercohomologyFunctor (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s) q,
      ∀ B : DerivedCategory.Plus (EtSheaves P X),
        k.app B ≫ (Sheaf.supportHypercohomologyInclusion
          (Scheme.ProEt.topology X) (Modules P) (supportRestrictionArrow s) q).app
            ((nuPlus P X).obj B) =
        (hyper P Y q).map ((nu P Y).map
          ((Etale.lowerStar (Modules P) p).rightDerivedFunctor.map
            ((Adjunction.ofIsLeftAdjoint
              (Etale.lowerStar (Modules P) s).rightDerivedFunctor).counit.app B.obj)) ≫
            imageComparison P p B) ≫
          (middleGlobalIso P p q).hom.app B := by
  obtain ⟨k, hk⟩ := sourceSupportMap_exists P p s
  let S := supportSections s P.Coefficient
  let H := DerivedCategory.homologyFunctor (Modules P) q
  let kq := Functor.whiskerRight k H ≫
    Functor.whiskerLeft (nuPlus P X)
      (Functor.isoWhiskerRight S.rightDerivedFunctorPlusCompatibility.symm H).hom
  refine ⟨kq, fun B ↦ ?_⟩
  have hn := NatTrans.congr_app (compatibility_naturality
    (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
      (supportRestrictionArrow s))) ((nuPlus P X).obj B)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hn
  have hn' : S.rightDerivedFunctorPlusCompatibility.inv.app ((nuPlus P X).obj B) ≫
      DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusNatTrans
        (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s))).app ((nuPlus P X).obj B)) =
    (Functor.rightDerivedFunctorNatTrans
        (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s))).app ((input P X).obj B) ≫
      (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility.inv.app
        ((nuPlus P X).obj B) := by
    let ec := (globalSectionsFunctor (Modules P) X).rightDerivedFunctorPlusCompatibility
    apply (cancel_mono (ec.hom.app ((nuPlus P X).obj B))).mp
    erw [Category.assoc, hn, Iso.inv_hom_id_app_assoc, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    rfl
  dsimp only [kq, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom]
  change H.map (k.app B) ≫ H.map _ ≫ H.map _ = _
  erw [← H.map_comp, hn', H.map_comp, ← H.map_comp_assoc, hk B, H.map_comp]
  simp only [middleGlobalIso, sectionPlusIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_inv, NatTrans.id_app,
    Functor.comp_map, Category.assoc]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The ordinary closed-adjoint kernel construction produces the natural support map.
Source: `lem-pur-supported-hom.proof.md` and the second assertion of
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-kernel-counit-map-existence).

Proof:
1. For a bounded-below injective etale complex I, the ordinary closed right adjoint
   preserves injectives since closed direct image is exact. Its sections are exactly
   the kernel of I(X) to I(U); the kernel inclusion is the closed counit. These are
   natural identifications of complexes, including their differentials.
2. Pass to the derived functors using their actual units. Compare the chosen right
   adjoint with the closed-support model by right-adjoint uniqueness. Compose with
   the global etale/pro-etale comparison. The retraction collapse and the invertible
   specified first comparison identify this source with global sections of closedTerm.
3. Apply the unit-normalized comparison of support kernels between the two sites.
   Naturality of the restriction square identifies its composite with forgetting
   support with the usual global comparison. Apply degree-two homology.
4. The hypothesis hfirst identifies the counit arrow after that source comparison
   with the specified first arrow. Naturality of the derived direct-image compositor
   identifies the global comparison with middleGlobalIso, giving the square. This
   construction applies also to zero inputs, empty T, and the zero coefficient ring. -/
theorem kernelCounitMap_exists
    (P : WeilConjectures.PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) [IsLocallyNoetherian (Line T)]
    (first : closedTerm P (zeroSection T) ⟶ middleTerm P (lineProjection T))
    (hfirstIso : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
      IsIso (firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) B))
    (hfirst : ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
      firstComparison P (lineProjection T) (zeroSection T)
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T) B ≫ first.app B =
        (nu P T).map ((Etale.lowerStar (Modules P) (lineProjection T)).rightDerivedFunctor.map
          ((Adjunction.ofIsLeftAdjoint
            (Etale.lowerStar (Modules P) (zeroSection T)).rightDerivedFunctor).counit.app B.obj)) ≫
          imageComparison P (lineProjection T) B) :
    ∃ κ : closedTerm P (zeroSection T) ⋙ hyper P T 2 ⟶
        nuPlus P (Line T) ⋙ Sheaf.supportHypercohomologyFunctor
          (Scheme.ProEt.topology (Line T)) (Modules P)
          (supportRestrictionArrow (zeroSection T)) 2,
      ∀ B : DerivedCategory.Plus (EtSheaves P (Line T)),
        (hyper P T 2).map (first.app B) ≫
            (middleGlobalIso P (lineProjection T) 2).hom.app B =
          κ.app B ≫ (Sheaf.supportHypercohomologyInclusion
            (Scheme.ProEt.topology (Line T)) (Modules P)
            (supportRestrictionArrow (zeroSection T)) 2).app ((nuPlus P (Line T)).obj B)  := by
  have _ramification := h
  let p := lineProjection T
  let s := zeroSection T
  let hs := AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) T
  let c := firstComparisonNat P p s hs
  have (B : DerivedCategory.Plus (EtSheaves P (Line T))) : IsIso (c.app B) := by
    change IsIso ((firstComparisonNat P p s hs).app B)
    rw [firstComparisonNat_app]
    exact hfirstIso B
  have : IsIso c := NatIso.isIso_of_isIso_app c
  obtain ⟨k, hk⟩ := sourceSupportHyperMap_exists P p s 2
  refine ⟨Functor.whiskerRight (asIso c).inv (hyper P T 2) ≫ k, fun B ↦ ?_⟩
  apply (cancel_epi ((hyper P T 2).map (c.app B))).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Category.assoc]
  have hi : (hyper P T 2).map (c.app B) ≫
      (hyper P T 2).map ((asIso c).inv.app B) = 𝟙 _ :=
    ((hyper P T 2).mapIso ((asIso c).app B)).hom_inv_id
  erw [reassoc_of% hi]
  erw [← (hyper P T 2).map_comp_assoc, firstComparisonNat_app, hfirst B]
  exact (hk B).symm

end AlgebraicGeometry.ProEtale.RetractedSupport
