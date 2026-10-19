/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Sheaf.Paper.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# Classicality of bounded-below direct images

Source: blueprint, direct-image comparison, proof step 5; Stacks Tag 09A6.
(blueprint: lem-pe-classical-direct-image-preservation).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
-- Restriction along constant scalar sections retains every underlying section.
private noncomputable def intrinsicRestriction (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} Λ)))) ⥤
      Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) where
  obj F := ⟨moduleSectionPresheaf Λ F,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1}) F.isSheaf⟩
  map f := { hom :=
    { app := fun W ↦ (ModuleCat.restrictScalars
        ((Functor.whiskerRight
          (toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app W).hom).map (f.val.app W)
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x } }

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Additive where
  map_add := by intros; ext W x; rfl

private noncomputable def intrinsicPresheaf (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) ⥤
      PresheafOfModules.{u + 1}
        ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Λ))) where
  obj F := { obj := F.obj
             map := F.map
             map_id W := by ext x; exact ConcreteCategory.congr_hom (F.map_id W) x
             map_comp f g := by ext x; exact ConcreteCategory.congr_hom (F.map_comp f g) x }
  map f := { app := f.app
             naturality g := by ext x; exact ConcreteCategory.congr_hom (f.naturality g) x }

-- Local surjectivity of constant sections makes scalar restriction fully faithful.
private noncomputable def intrinsicRestrictionFullyFaithful (X : Scheme.{u}) (Λ : Type u)
    [CommRing Λ] : (intrinsicRestriction X Λ).FullyFaithful := by
  let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).2
  exact {
    preimage {M N} f := ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    (Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) N.isSheaf).symm
        ((intrinsicPresheaf X Λ).map f.hom)⟩
    map_preimage := by intro M N f; ext W x; rfl
    preimage_map := by intro M N f; ext W x; rfl }

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Full := (intrinsicRestrictionFullyFaithful X Λ).full
private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).Faithful := (intrinsicRestrictionFullyFaithful X Λ).faithful

-- Sheafification supplies the inverse on objects; its unit is already an isomorphism.
private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).EssSurj where
  mem_essImage F := by
    let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).1
    let := (Scheme.proEtaleConstantRingUnit_locallyBijective X Λ).2
    let R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing X Λ)
    let α : (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} Λ)) ⟶ R.obj :=
      Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let P := (intrinsicPresheaf X Λ).obj F.obj
    let M := (PresheafOfModules.sheafification.{u + 1} (R := R) α).obj P
    let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} (R := R) α).unit.app P
    let η' : F ⟶ (intrinsicRestriction X Λ).obj M :=
      { hom := { app := η.app
                 naturality := fun {_ _} f ↦ by
                   ext x
                   exact PresheafOfModules.naturality_apply η f x } }
    have hη : IsIso η := by
      apply (isIso_iff_of_reflects_iso η (PresheafOfModules.toPresheaf _)).mp
      change IsIso (toSheafify (Scheme.ProEt.topology X) P.presheaf)
      exact isIso_toSheafify _ ((sheafCompose _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})).obj F).property
    have : IsIso η := hη
    have : IsIso η' := by
      apply (isIso_iff_of_reflects_iso η' (sheafToPresheaf _ _)).mp
      change IsIso η'.hom
      have (W : X.ProEtᵒᵖ) : IsIso (η'.hom.app W) := by
        apply (isIso_iff_of_reflects_iso _
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})).mp
        change IsIso (((PresheafOfModules.toPresheaf _).map η).app W)
        infer_instance
      exact NatIso.isIso_of_isIso_app _
    exact ⟨M, ⟨(asIso η').symm⟩⟩

private noncomputable instance (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    (intrinsicRestriction X Λ).IsEquivalence := {}

private theorem coefficientUnit_comp {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] (W : Y.ProEtᵒᵖ) (a : ULift.{u + 1, u} Λ) :
    (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))).app
        ((Scheme.proEtaleBaseChange g).op.obj W) a := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))
    ((Scheme.proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj
      (Scheme.proEtaleConstantRing X Λ))).apply_symm_apply
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange g).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} Λ)))))
  rw [Adjunction.homEquiv_unit] at h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h W) a

-- The section functions are identities; the coefficient-unit equation proves linearity.
private noncomputable def restrictionDirectImageIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] :
    Scheme.proEtaleConstantModuleDirectImage g Λ ⋙ intrinsicRestriction Y Λ ≅
      intrinsicRestriction X Λ ⋙ lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
    refine NatIso.ofComponents (fun W ↦ ?_) ?_
    · let L := ((intrinsicRestriction Y Λ).obj
          ((Scheme.proEtaleConstantModuleDirectImage g Λ).obj M)).obj.obj W
      let R := ((intrinsicRestriction X Λ).obj M).obj.obj
          ((Scheme.proEtaleBaseChange g).op.obj W)
      let h : L ⟶ R := ModuleCat.ofHom (X := L) (Y := R)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            change (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
              ((toSheafify (Scheme.ProEt.topology Y)
                ((Functor.const Y.ProEtᵒᵖ).obj
                  (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) •
                  (show M.val.obj ((Scheme.proEtaleBaseChange g).op.obj W) from x) = _
            rw [coefficientUnit_comp]
            rfl }
      let i : R ⟶ L := ModuleCat.ofHom (X := R) (Y := L)
        { toFun := fun x ↦ x
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro a x
            change _ = (Scheme.proEtaleCoefficientDirectImageMap g Λ).hom.app W
              ((toSheafify (Scheme.ProEt.topology Y)
                ((Functor.const Y.ProEtᵒᵖ).obj
                  (CommRingCat.of (ULift.{u + 1, u} Λ)))).app W a) •
                  (show M.val.obj ((Scheme.proEtaleBaseChange g).op.obj W) from x)
            rw [coefficientUnit_comp]
            rfl }
      exact { hom := h, inv := i
              hom_inv_id := by ext x; rfl
              inv_hom_id := by ext x; rfl }
    · intro U V f
      ext x
      rfl
  · intro M N f
    ext W x
    rfl

private theorem classicalFor_iso_iff (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)} (e : F ≅ G) :
    IsClassicalModuleFor X Λ F ↔ IsClassicalModuleFor X Λ G := by
  have h {F G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)}
      (e : F ≅ G) (hF : IsClassicalModuleFor X Λ F) : IsClassicalModuleFor X Λ G := by
    intro I _ _ P
    have hmap := continuityMap_natural P e.hom.hom
    have : IsIso (continuityMap P F.obj) := hF P
    have : IsIso (Functor.whiskerLeft P.diagram.op e.hom.hom) := by
      change IsIso (Functor.isoWhiskerLeft P.diagram.op
        ((sheafToPresheaf _ _).mapIso e)).hom
      infer_instance
    apply (isIso_comp_left_iff
      (colimMap (Functor.whiskerLeft P.diagram.op e.hom.hom)) _).mp
    rw [hmap]
    infer_instance
  exact ⟨h e, h e.symm⟩

private theorem classicalComplexFor_iso_iff (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]
    {F G : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (e : F ≅ G) : IsClassicalComplexFor X Λ F ↔ IsClassicalComplexFor X Λ G := by
  apply forall_congr'
  intro q
  exact classicalFor_iso_iff X Λ
    ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).mapIso
      ((ShrinkHoms.equivalence _).inverse.mapIso e))

private theorem fixedClassicalDirectImage (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (M : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (hc : ClassicalPlus X Λ M) :
    ClassicalPlus Y Λ
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj M) := by
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  have hu (Z : Scheme.{u}) := (boundedBelowComparison Z Λ).1
  have he (Z : Scheme.{u}) := classicalDerivedEquivalence Z Λ
    (fun K ↦ by let := hu Z; infer_instance)
  have hε := (he X).2.1 M hc
  let e := asIso ((comparisonAdjunction (ModuleCat.{u + 1} Λ) X).derivedPlus.counit.app M)
  let K := (comparisonLowerStar (ModuleCat.{u + 1} Λ) X).rightDerivedFunctorPlus.obj M
  have hi : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ))) := by
    have := isIso_lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)
    exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective
        (ModuleCat.{u + 1} Λ) g I)
  let c := asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} Λ)))
  let d := c.app K ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.mapIso e
  exact (classicalComplexFor_iso_iff Y Λ (DerivedCategory.Plus.ι.mapIso d)).mp
    ((he Y).1 ((Etale.lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.obj K))

@[instance_reducible]
private noncomputable def intrinsicHasDerivedCategory (X : Scheme.{u}) (Λ : Type u) [CommRing Λ] :
    HasDerivedCategory (SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing X Λ))) :=
  HasDerivedCategory.standard _

attribute [local instance] intrinsicHasDerivedCategory

private noncomputable def restrictionDerivedDirectImageIso {X Y : Scheme.{u}}
    (g : X ⟶ Y) (Λ : Type u) [CommRing Λ] :
    (Scheme.proEtaleConstantDerivedDirectImage g Λ) ⋙
        (intrinsicRestriction Y Λ).mapDerivedCategory ≅
      (intrinsicRestriction X Λ).mapDerivedCategory ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    (Scheme.proEtaleConstantModuleDirectImage g Λ) (intrinsicRestriction Y Λ)).symm ≪≫
    Functor.rightDerivedFunctorNatIso (restrictionDirectImageIso g Λ) ≪≫
    Functor.rightDerivedFunctorCompIso (intrinsicRestriction X Λ)
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) ≪≫
    Functor.isoWhiskerRight (intrinsicRestriction X Λ).rightDerivedFunctorIsoMapDerivedCategory
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g).rightDerivedFunctor

-- Compare the smaller localization with the standard model used by classicality.
private noncomputable def fixedHomologyStandardIso (X : Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (q : ℤ) :
    DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) q ≅
      (ShrinkHoms.equivalence.{u + 1}
        (@DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _))).inverse ⋙
        @DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
          _ _ (HasDerivedCategory.standard _) q := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let Qs := @DerivedCategory.Q C _ _ (HasDerivedCategory.standard _)
  let Hs := @DerivedCategory.homologyFunctor C _ _ (HasDerivedCategory.standard _) q
  let e := ShrinkHoms.equivalence.{u + 1} (@DerivedCategory C _ _ (HasDerivedCategory.standard _))
  let hi : DerivedCategory.Q ⋙ e.inverse ≅ Qs :=
    (Functor.associator Qs e.functor e.inverse).symm ≪≫
      Functor.isoWhiskerLeft Qs e.unitIso.symm ≪≫ Functor.rightUnitor Qs
  apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) C).preimageIso
  exact DerivedCategory.homologyFunctorFactors C q ≪≫
    (@DerivedCategory.homologyFunctorFactors C _ _ (HasDerivedCategory.standard _) q).symm ≪≫
    (Functor.isoWhiskerRight hi Hs).symm ≪≫ Functor.associator _ _ _

private theorem restrictionClassical_iff (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]
    (M : Scheme.proEtaleDerivedCategory X Λ) :
    IsClassicalComplex Λ M ↔ IsClassicalComplexFor X (ULift.{u + 1, u} Λ)
      ((intrinsicRestriction X Λ).mapDerivedCategory.obj M) := by
  apply forall_congr'
  intro q
  have he := ((intrinsicRestriction X Λ).mapDerivedCategoryHomologyFunctorIso q).app M ≪≫
    (fixedHomologyStandardIso X (ULift.{u + 1, u} Λ) q).app
      ((intrinsicRestriction X Λ).mapDerivedCategory.obj M)
  change IsClassicalModuleFor X (ULift.{u + 1, u} Λ)
    ((intrinsicRestriction X Λ).obj
      ((@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q).obj M)) ↔ _
  exact classicalFor_iso_iff X (ULift.{u + 1, u} Λ) he


/-- Direct image preserves classicality for bounded-below complexes and qcqs maps.
Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-thm-pe-direct-image-comparison/_section.md, classicality consequence;
sk-cor-pe-classical-derived/_section.md, derived equivalence; Stacks Tag 09A6.
(blueprint: lem-pe-classical-direct-image-preservation).

Proof: Realize sheaves valued in modules over the discrete constant ring as modules
on the ringed pro-etale site, using their sectionwise constant scalar actions. This
exact equivalence and its inverse commute with cohomology and preserve lower bounds.
They identify the continuity predicates: their section maps identify the diagrams and
the canonical colimit-to-sections maps for each affine presentation. They also identify
module direct image, since both evaluate a sheaf on the same base-changed object with
the same constant-section scalar action. Deriving gives the corresponding identification
of ordinary uncompleted direct images on bounded-below complexes, by injective resolutions.
In fixed-scalar coordinates, the bounded-below comparison unit is invertible by
sk-prop-sf-comparison. The classical derived equivalence therefore identifies the given
classical M with nu_X^* K for a bounded-below etale K, by its counit. Apply derived
direct image and the qcqs direct-image comparison to identify its image with
nu_Y^* Rg_et,* K. The etale derived direct image is bounded below, and the other
clause of the classical derived equivalence says this comparison pullback is classical.
Transport back through the section-normalized equivalence. Classicality is invariant
under each isomorphism: on cohomology, naturality conjugates every continuity map by
an invertible section map and the colimit of invertible stage maps. Thus its continuity
map is invertible for every degree and every affine presentation. This also covers
the zero coefficient ring, empty schemes, and arbitrary cohomological lower bounds. -/
theorem classicalDirectImagePreservation
    (Λ : Type u) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [QuasiCompact g] [QuasiSeparated g]
    (M : Scheme.proEtaleDerivedCategory X Λ)
    (hM : ∃ n : ℤ, DerivedCategory.IsGE M n)
    (hc : IsClassicalComplex (X := X) Λ M) :
    IsClassicalComplex (X := Y) Λ
      ((Scheme.proEtaleConstantDerivedDirectImage g Λ).obj M) := by
  let N := (intrinsicRestriction X Λ).mapDerivedCategory.obj M
  have hN : ∃ n : ℤ, DerivedCategory.IsGE N n := by
    obtain ⟨n, hn⟩ := hM
    let := hn
    exact ⟨n, (intrinsicRestriction X Λ).isGE_mapDerivedCategory_obj M n⟩
  let Np : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))) :=
    ⟨N, hN⟩
  have hcN : ClassicalPlus X (ULift.{u + 1, u} Λ) Np :=
    (restrictionClassical_iff X Λ M).mp hc
  have hd := fixedClassicalDirectImage (ULift.{u + 1, u} Λ) g Np hcN
  let e := (restrictionDerivedDirectImageIso g Λ).app M
  let d := Functor.rightDerivedFunctorPlusCompatibility
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) g) |>.app Np
  apply (restrictionClassical_iff Y Λ _).mpr
  exact (classicalComplexFor_iso_iff Y (ULift.{u + 1, u} Λ) (d ≪≫ e.symm)).mp hd

end AlgebraicGeometry.ProEtale
