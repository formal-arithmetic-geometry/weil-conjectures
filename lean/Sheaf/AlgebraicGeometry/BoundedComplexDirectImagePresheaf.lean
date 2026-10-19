/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-!
# The presheaf description of bounded-below higher direct images

Source: Stacks Project, Tag 0D6I, lemma-unbounded-describe-higher-direct-images,
and the first paragraph of the blueprint det-pe-bounded-continuity-direct-image
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).

All coefficient sheaves, complexes, presheaves and conclusions use the original
small pro-etale sites. The AsSmall model is used only to construct resolutions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- The standard localization of module complexes at quasi-isomorphisms, as in the
recorded derived category of an abelian category.
Source: Stacks Project, Tag 05RU (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable instance boundedDirectImageModules_hasDerivedCategory {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) :=
  HasDerivedCategory.standard _

/-- Transparent Mathlib pushforward specialization over the direct-image coefficient sheaf.
It is definitionally the landed ringModuleDirectImage, as checked with its consumer.
Source: the Weil conjectures blueprint, `lem-pe-bounded-complex-direct-image-presheaf`
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable abbrev boundedRingModuleDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    SheafOfModules.{u + 1} R ⥤
      SheafOfModules.{u + 1} ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := topology Y) (K := topology X)
    (S := (proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
    (R := R) (𝟙 _)

/-- Sectionwise additivity of direct image. Source: Stacks Tag 03D1
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance boundedRingModuleDirectImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (boundedRingModuleDirectImage f R).Additive :=
  ⟨by intros; rfl⟩

/-- Sectionwise additivity of transport back to the original site.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance ringModuleFromModel_additive {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleFromModel R).Additive := ⟨by intros; rfl⟩

/-- Sectionwise additivity of transport to the model.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance ringModuleToModel_additive {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).Additive := ⟨by intros; rfl⟩

/-- The sectionwise identity identifies round-trip transport with the original modules.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelRoundTrip {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    𝟭 (ringedSiteModules.{u + 1} R) ≅
      proEtaleModuleToModel R ⋙ proEtaleModuleFromModel R :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _)))

/-- The model replacement used by the landed ringHypercohomology, before transport back.
Source: Stacks Tag 079P (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelResolutionFunctor {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    CochainComplex.kInjectiveResolutionFunctor.{u + 1} (ringedSiteModules.{u + 1} S)

/-- One functorial resolution on the original site, transported from the small model.
Source: Stacks Tags 079P and 03D1
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleResolutionFunctor {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤
      CochainComplex (ringedSiteModules.{u + 1} R) ℤ :=
  ringModuleModelResolutionFunctor R ⋙
    (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual augmentation of the transported functorial resolution.
Source: Stacks Tags 079P and 03D1
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleResolutionMap {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1})
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
    K ⟶ (ringModuleResolutionFunctor R).obj K :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  let A := (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  let B := (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  let s : A.obj K ⟶ (CochainComplex.kInjectiveResolutionFunctor.{u + 1}
      (ringedSiteModules.{u + 1} S)).obj (A.obj K) :=
    (CochainComplex.toKInjectiveResolution.{u + 1} (ringedSiteModules.{u + 1} S)).app
      (A.obj K)
  ((Functor.mapHomologicalComplexIdIso (ringedSiteModules.{u + 1} R)
      (ComplexShape.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (ringModuleModelRoundTrip R) (ComplexShape.up ℤ)).hom.app K ≫
    B.map s

/-- The specified transported complex and augmentation form a K-injective resolution.
Source: Stacks Tags 079P, 03D1 and 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).
Proof: the sectionwise transports to and from AsSmall are inverse additive equivalences.
They preserve acyclic complexes, chain homotopies and quasi-isomorphisms. The model
module category is Grothendieck, so its published functorial replacement is K-injective
and its augmentation a quasi-isomorphism. Transporting its Hom vanishing against every
acyclic complex proves K-injectivity back on the original site. The transported
augmentation is exactly ringModuleResolutionMap, since the round-trip on sections is
the identity. Thus both assertions hold without any resolution-existence hypothesis. -/
theorem ringModuleResolution_isKInjective_quasiIso {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1})
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
    ((ringModuleResolutionFunctor R).obj K).IsKInjective ∧
      QuasiIso (ringModuleResolutionMap R K) := by
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  let := SheafOfModules.isGrothendieckAbelian S
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsContinuous
      (topology X) (proEtaleModelTopology X) := proEtaleModelUp_isContinuous X
  let : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsContinuous
      (proEtaleModelTopology X) (topology X) := by
    change AsSmall.down.IsContinuous (proEtaleModelTopology X) (topology X)
    infer_instance
  let e : SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R :=
    SheafOfModules.pushforwardPushforwardEquivalence
      (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)) (𝟙 R) (𝟙 S)
      (by ext U; dsimp [AsSmall.equiv]; erw [S.obj.map_id]; rfl)
      (by ext U; dsimp [AsSmall.equiv]; erw [R.obj.map_id]; rfl)
  let : (proEtaleModuleFromModel R).IsEquivalence :=
    inferInstanceAs e.functor.IsEquivalence
  constructor
  · change CochainComplex.IsKInjective
      (((proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.kInjectiveResolutionFunctor.{u + 1}
          (ringedSiteModules.{u + 1} S)).obj
            (((proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))
    infer_instance
  · let A := (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)
    let B := (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)
    let s := (CochainComplex.toKInjectiveResolution.{u + 1}
      (ringedSiteModules.{u + 1} S)).app (A.obj K)
    have : QuasiIso s := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
      (ringedSiteModules.{u + 1} S) (A.obj K)).2
    have : QuasiIso (B.map s) := inferInstance
    change QuasiIso (_ ≫ B.map s)
    exact quasiIso_comp _ (B.map s)

/-- K-injective resolutions on the original site, with the explicit transported witness.
Source: Stacks Tag 079P (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable abbrev boundedRingModuleDirectImage_hasKInjectiveResolutions {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    ∀ K : CochainComplex (SheafOfModules.{u + 1} R) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u + 1} R) ℤ) (s : K ⟶ I),
        I.IsKInjective ∧ QuasiIso s :=
  fun K ↦ ⟨(ringModuleResolutionFunctor R).obj K, ringModuleResolutionMap R K,
    ringModuleResolution_isKInjective_quasiIso R K⟩

/-- Transparent specialization of the recorded right-derived construction.
It is definitionally the landed ringDerivedDirectImage, by proof irrelevance of witnesses.
Source: the Weil conjectures blueprint, `lem-pe-bounded-complex-direct-image-presheaf`
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable abbrev boundedRingDerivedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      DerivedCategory (SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)) :=
  Functor.rightDerivedFunctorOfQuasiIsoResolutions (boundedRingModuleDirectImage f R)
    (by
      let h := boundedRingModuleDirectImage_hasKInjectiveResolutions R
      exact fun L : CochainComplex (SheafOfModules.{u + 1} R) ℤ ↦
        h L)

/-- The recorded right-derived functor followed by degree-q homology.
It is definitionally the landed ringHigherDirectImage on the original site.
Source: the Weil conjectures blueprint, `lem-pe-bounded-complex-direct-image-presheaf`
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable abbrev boundedRingHigherDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} R) ⥤
      SheafOfModules.{u + 1}
        ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R) :=
  boundedRingDerivedDirectImage f R ⋙
    DerivedCategory.homologyFunctor _ q

/-- Underlying abelian presheaf sections after transport back and direct image.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageModuleSections {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :=
  proEtaleModuleFromModel R ⋙ boundedRingModuleDirectImage f R ⋙ SheafOfModules.toSheaf _ ⋙
    sheafToPresheaf (topology Y) AddCommGrpCat.{u + 1}

/-- Sectionwise additivity of inverse-image sections.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance inverseImageModuleSections_additive {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    (inverseImageModuleSections f R).Additive := ⟨by intros; rfl⟩

/-- Evaluation on the model, forgetting only the sectionwise module action.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def ringModuleModelEvaluation {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  SheafOfModules.evaluation S (op (AsSmall.up.obj U)) ⋙
    forget₂ (ModuleCat.{u + 1} (S.obj.obj (op (AsSmall.up.obj U)))) AddCommGrpCat.{u + 1}

/-- Sectionwise evaluation is additive.
Source: Stacks Tag 03D1 (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
instance ringModuleModelEvaluation_additive {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :
    (ringModuleModelEvaluation R U).Additive := ⟨by intros; rfl⟩

/-- Sectionwise direct image and transport evaluate to the same model sections.
Source: Stacks Tags 03D1 and 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageModuleEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (V : Y.ProEt) :
    inverseImageModuleSections f R ⋙
        (CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj (op V) ≅
      ringModuleModelEvaluation R ((proEtaleBaseChange f).obj V) :=
  NatIso.ofComponents (fun M ↦ Iso.refl _)

/-- The inverse-image section complex of the same model resolution.
Its terms are the underlying abelian sheaves of direct image of the transported resolution.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageSectionComplex {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    CochainComplex (ringedSiteModules.{u + 1} R) ℤ ⥤
      CochainComplex (Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ :=
  ringModuleModelResolutionFunctor R ⋙
    (inverseImageModuleSections f R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The sectionwise homology presheaf of the one resolution, before naming its values.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def resolvedInverseImageCohomologyPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :=
  inverseImageSectionComplex f R ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight _ _ _).obj
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q)

/-- The degreewise identity identifies the evaluated complex with model evaluation.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageSectionEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (V : Y.ProEt)
    (I : CochainComplex _ ℤ) :
    (((inverseImageModuleSections f R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).asFunctor.obj (op V) ≅
      (((ringModuleModelEvaluation R ((proEtaleBaseChange f).obj V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (inverseImageModuleEvaluationIso f R V).app (I.X n))

/-- Sectionwise homology is the published ringHypercohomology of the same resolution.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def resolvedInverseImageCohomologyEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) (V : Y.ProEt)
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
    ((resolvedInverseImageCohomologyPresheaf f R q).obj K).obj (op V) ≅
      (ringHypercohomology X R ((proEtaleBaseChange f).obj V) q).obj K :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso
    (inverseImageSectionEvaluationIso f R V ((ringModuleModelResolutionFunctor R).obj K))

/-- The section comparison respects maps of the input complex.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf).
Proof: the degreewise identity comparison is natural for every map of module complexes.
Apply the homology functor to that commutative square, and use preservation of
composition. Both resolution functors are the very same model replacement. -/
theorem resolvedInverseImageCohomologyEvaluation_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) (V : Y.ProEt)
    {K L : CochainComplex (ringedSiteModules.{u + 1} R) ℤ} (t : K ⟶ L) :
    ((resolvedInverseImageCohomologyPresheaf f R q).map t).app (op V) ≫
        (resolvedInverseImageCohomologyEvaluation f R q V L).hom =
      (resolvedInverseImageCohomologyEvaluation f R q V K).hom ≫
        (ringHypercohomology X R ((proEtaleBaseChange f).obj V) q).map t := by
  change (HomologicalComplex.homologyFunctor _ _ q).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ q).map _ =
    (HomologicalComplex.homologyFunctor _ _ q).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ q).map _
  simp only [← Functor.map_comp]
  congr 1

/-- The actual natural comparison to the landed hypercohomology functor at V.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def resolvedInverseImageCohomologyEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) (V : Y.ProEt) :
    (resolvedInverseImageCohomologyPresheaf f R q).flip.obj (op V) ≅
      ringHypercohomology X R ((proEtaleBaseChange f).obj V) q :=
  NatIso.ofComponents (resolvedInverseImageCohomologyEvaluation f R q V)
    (fun t ↦ resolvedInverseImageCohomologyEvaluation_naturality f R q V t)

/-- The presheaf with literally the landed hypercohomology functors as its values.
Restrictions are the resolved restrictions transported along the identity section comparison.
The copyObj construction also retains exactly ringHypercohomology.map on complex morphisms.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageCohomologyPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :=
  ((resolvedInverseImageCohomologyPresheaf f R q).flip.copyObj
    (fun V ↦ ringHypercohomology X R ((proEtaleBaseChange f).obj V.unop) q)
    (fun V ↦ resolvedInverseImageCohomologyEvaluationIso f R q V.unop)).flip

/-- The chosen presentation of the presheaf by resolved sectionwise homology.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def inverseImageCohomologyPresheafIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :
    resolvedInverseImageCohomologyPresheaf f R q ≅ inverseImageCohomologyPresheaf f R q :=
  Functor.flipping.functor.mapIso
    ((resolvedInverseImageCohomologyPresheaf f R q).flip.isoCopyObj
      (fun V ↦ ringHypercohomology X R ((proEtaleBaseChange f).obj V.unop) q)
      (fun V ↦ resolvedInverseImageCohomologyEvaluationIso f R q V.unop))

/-- Exact abelian sheafification identifies sectionwise homology with sheaf homology.
The map is the exact-functor homology comparison followed by the sheafification counit.
Source: Stacks, proof of lemma-sheafification-cohomology, Tag 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def sectionHomologySheafificationIso {Y : Scheme.{u}}
    (B : CochainComplex (Sheaf (topology Y) AddCommGrpCat.{u + 1}) ℤ)
    (q : ℤ) :
    (presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}).obj
        ((((sheafToPresheaf (topology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj B).homology q) ≅ B.homology q :=
  let J := topology Y
  let A := AddCommGrpCat.{u + 1}
  let C := ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.up ℤ)).obj B
  ((C.sc q).mapHomologyIso (presheafToSheaf J A)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      ((NatIso.mapHomologicalComplex
        (asIso (sheafificationAdjunction J A).counit) (ComplexShape.up ℤ)).app B)


/-- The exact evaluation homology comparison commutes with every restriction.
Source: Stacks, proof of lemma-sheafification-cohomology, Tag 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).
Proof: for each evaluation functor use ShortComplex.mapHomologyIso. An arrow of the
site induces a natural transformation of these exact evaluations. Apply
ShortComplex.homologyMap_mapNatTrans to the degree-q short complex; cancel the
inverse comparison on the right. This gives exactly the displayed restriction
identity, including empty objects and all integer degrees. -/
theorem sectionHomologyPresheaf_naturality {Y : Scheme.{u}}
    (C : CochainComplex (Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ) (q : ℤ)
    {V W : Y.ProEtᵒᵖ} (a : V ⟶ W) :
    (C.asFunctor ⋙ HomologicalComplex.homologyFunctor _ _ q).map a ≫
        ((C.sc q).mapHomologyIso
          ((CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj W)).hom =
      ((C.sc q).mapHomologyIso
        ((CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj V)).hom ≫
        (C.homology q).map a := by
  let τ := (CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).map a
  have h := ShortComplex.homologyMap_mapNatTrans (C.sc q) τ
  change ShortComplex.homologyMap ((C.sc q).mapNatTrans τ) ≫ _ = _
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Sectionwise cohomology is canonically the homology presheaf, using exact evaluation.
Source: Stacks, proof of lemma-sheafification-cohomology, Tag 0D6I
(blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def sectionHomologyPresheafIso {Y : Scheme.{u}}
    (C : CochainComplex (Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℤ) (q : ℤ) :
    C.asFunctor ⋙ HomologicalComplex.homologyFunctor _ _ q ≅ C.homology q :=
  NatIso.ofComponents
    (fun V ↦ (C.sc q).mapHomologyIso
      ((CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj V))
    (fun a ↦ sectionHomologyPresheaf_naturality C q a)

/-- The canonical composed isomorphism on the original pro-etale sites.
Its factors are pointwise homology, exact sheafification and its counit, exact
forgetting of modules, and the unit comparison of the recorded right derived functor.
Source: Stacks Tag 0D6I (blueprint: lem-pe-bounded-complex-direct-image-presheaf). -/
noncomputable def boundedComplexDirectImagePresheafIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ)
    (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (_hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.X n)) :
    (presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}).obj
        ((inverseImageCohomologyPresheaf f R q).obj K) ≅
      (SheafOfModules.toSheaf _).obj
        ((boundedRingHigherDirectImage f R q).obj (DerivedCategory.Q.obj K)) :=
  let I := (ringModuleResolutionFunctor R).obj K
  let s := ringModuleResolutionMap R K
  letI : I.IsKInjective := (ringModuleResolution_isKInjective_quasiIso R K).1
  letI : QuasiIso s := (ringModuleResolution_isKInjective_quasiIso R K).2
  let F := boundedRingModuleDirectImage f R
  let T := SheafOfModules.toSheaf.{u + 1}
    ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
  letI : PreservesFiniteLimits T := (moduleSheaves_colimits_forgetful _).2.1
  letI : PreservesFiniteColimits T := (moduleSheaves_colimits_forgetful _).2.2.1
  let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I
  let B := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  (presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}).mapIso
      ((inverseImageCohomologyPresheafIso f R q).app K).symm ≪≫
    (presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}).mapIso
      (sectionHomologyPresheafIso
        (((sheafToPresheaf (topology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj B) q) ≪≫
    sectionHomologySheafificationIso B q ≪≫
    (C.sc q).mapHomologyIso T ≪≫
    T.mapIso ((DerivedCategory.homologyFunctorFactors _ q).app C).symm ≪≫
    T.mapIso ((DerivedCategory.homologyFunctor _ q).mapIso
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso
        (boundedRingModuleDirectImage_hasKInjectiveResolutions R) s)).symm

private noncomputable def ringModuleResolutionAugmentation {X : Scheme.{u}}
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    𝟭 (CochainComplex (ringedSiteModules.{u + 1} R) ℤ) ⟶ ringModuleResolutionFunctor R :=
  let S := ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology X) (topology X)).obj R
  letI := SheafOfModules.isGrothendieckAbelian S
  let A := (proEtaleModuleToModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  let B := (proEtaleModuleFromModel R).mapHomologicalComplex (ComplexShape.up ℤ)
  ((Functor.mapHomologicalComplexIdIso (ringedSiteModules.{u + 1} R)
      (ComplexShape.up ℤ)).symm ≪≫
    NatIso.mapHomologicalComplex (ringModuleModelRoundTrip R) (ComplexShape.up ℤ)).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft A
      (CochainComplex.toKInjectiveResolution.{u + 1} (ringedSiteModules.{u + 1} S))) B

private noncomputable def sectionHomologyPresheafNatIso {Y : Scheme.{u}} (q : ℤ) :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight Y.ProEtᵒᵖ _ _).obj
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ) q) ≅
      HomologicalComplex.homologyFunctor (Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ) q :=
  NatIso.ofComponents (fun C ↦ sectionHomologyPresheafIso C q) (fun t ↦ by
    apply NatTrans.ext
    funext V
    exact ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ q).map t)
      ((CategoryTheory.evaluation Y.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj V))

private noncomputable def exactHomologyNatIso
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (q : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) q ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc q).mapHomologyIso F)
    (fun t ↦ ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor _ _ q).map t) F)

private noncomputable def sectionHomologySheafificationNatIso {Y : Scheme.{u}} (q : ℤ) :
    (sheafToPresheaf (topology Y) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q ⋙
        presheafToSheaf (topology Y) AddCommGrpCat.{u + 1} ≅
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q :=
  let U := sheafToPresheaf (topology Y) AddCommGrpCat.{u + 1}
  let A := presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}
  let E : U.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        A.mapHomologicalComplex (ComplexShape.up ℤ) ≅ 𝟭 _ :=
    NatIso.mapHomologicalComplex (asIso (sheafificationAdjunction
      (topology Y) AddCommGrpCat.{u + 1}).counit) (ComplexShape.up ℤ)
  Functor.isoWhiskerLeft (U.mapHomologicalComplex (ComplexShape.up ℤ))
      (exactHomologyNatIso A q).symm ≪≫
    Functor.isoWhiskerRight E (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) q)

private theorem derivedResolutionComparison_naturality
    {C : Type*} {D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (h : ∀ K : CochainComplex C ℤ,
      ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)
    {K L I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective]
    (s : K ⟶ I) (r : L ⟶ J) [QuasiIso s] [QuasiIso r]
    (t : K ⟶ L) (g : I ⟶ J) (w : t ≫ r = s ≫ g) :
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Q.map t) ≫
        (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h r).hom =
      (F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso h s).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions h
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  let H := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h J
  have hw : RF.map (DerivedCategory.Q.map t) ≫ RF.map (DerivedCategory.Q.map r) =
      RF.map (DerivedCategory.Q.map s) ≫ RF.map (DerivedCategory.Q.map g) := by
    simp only [← Functor.map_comp, w]
  have hn := η.naturality (H.map g)
  dsimp only [Functor.comp_map] at hn
  have hq := congrArg RF.map ((DerivedCategory.quotientCompQhIso C).inv.naturality g)
  dsimp only [Functor.comp_map] at hq
  simp only [Functor.map_comp] at hq
  have hu : RF.map (DerivedCategory.Qh.map (H.map g)) ≫ inv (η.app (H.obj J)) =
      inv (η.app (H.obj I)) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (H.map g)) := by
    apply (cancel_epi (η.app (H.obj I))).1
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  have hf := (DerivedCategory.quotientCompQhIso D).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map g)
  dsimp only [Functor.comp_map] at hf
  dsimp only [Functor.rightDerivedFunctorOfQuasiIsoResolutionsObjIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, asIso_hom, asIso_inv]
  change RF.map (DerivedCategory.Q.map t) ≫
      (RF.map (DerivedCategory.Q.map r) ≫
        RF.map ((DerivedCategory.quotientCompQhIso C).inv.app J) ≫
        inv (η.app (H.obj J)) ≫ (DerivedCategory.quotientCompQhIso D).hom.app _) = _
  simp only [Category.assoc]
  rw [reassoc_of% hw, reassoc_of% hq, reassoc_of% hu]
  dsimp only [H] at hu ⊢
  simp only [Functor.mapHomotopyCategory_map] at *
  simpa only [HomotopyCategory.quotient_obj_as, H, RF, η, Iso.app_inv,
    Category.assoc] using congrArg
    (fun k ↦ RF.map (DerivedCategory.Q.map s) ≫
    RF.map ((DerivedCategory.quotientCompQhIso C).inv.app I) ≫
      inv (η.app (H.obj I)) ≫ k) hf

private noncomputable def ringDirectImageResolutionNatIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) :
    DerivedCategory.Q ⋙ boundedRingDerivedDirectImage f R ≅
      ringModuleResolutionFunctor R ⋙
        (boundedRingModuleDirectImage f R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q := by
  letI (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
      ((ringModuleResolutionFunctor R).obj K).IsKInjective :=
    (ringModuleResolution_isKInjective_quasiIso R K).1
  letI (K : CochainComplex (ringedSiteModules.{u + 1} R) ℤ) :
      QuasiIso (ringModuleResolutionMap R K) :=
    (ringModuleResolution_isKInjective_quasiIso R K).2
  exact NatIso.ofComponents (fun K ↦
    (boundedRingModuleDirectImage f R).rightDerivedFunctorOfQuasiIsoResolutionsObjIso
      (boundedRingModuleDirectImage_hasKInjectiveResolutions R) (ringModuleResolutionMap R K))
    (fun t ↦ derivedResolutionComparison_naturality _ _ _ _ t
      ((ringModuleResolutionFunctor R).map t) ((ringModuleResolutionAugmentation R).naturality t))

private noncomputable def boundedComplexDirectImagePresheafNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ) :
    inverseImageCohomologyPresheaf f R q ⋙
        presheafToSheaf (topology Y) AddCommGrpCat.{u + 1} ≅
      (DerivedCategory.Q ⋙ boundedRingHigherDirectImage f R q) ⋙
        SheafOfModules.toSheaf _ := by
  let F := boundedRingModuleDirectImage f R
  let T := SheafOfModules.toSheaf.{u + 1}
    ((proEtaleSheafDirectImage f RingCat.{u + 1}).obj R)
  letI : PreservesFiniteLimits T := (moduleSheaves_colimits_forgetful _).2.1
  letI : PreservesFiniteColimits T := (moduleSheaves_colimits_forgetful _).2.2.1
  let C := ringModuleResolutionFunctor R ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)
  let B := C ⋙ T.mapHomologicalComplex (ComplexShape.up ℤ)
  let A := presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}
  exact Functor.isoWhiskerRight (inverseImageCohomologyPresheafIso f R q).symm A ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (inverseImageSectionComplex f R)
        (sectionHomologyPresheafNatIso q)) A ≪≫
    Functor.isoWhiskerLeft B (sectionHomologySheafificationNatIso q) ≪≫
    Functor.isoWhiskerLeft C
      (exactHomologyNatIso T q) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft C (DerivedCategory.homologyFunctorFactors _ q).symm) T ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (ringDirectImageResolutionNatIso f R).symm
        (DerivedCategory.homologyFunctor _ q)) T

/-- The canonical isomorphisms are natural for every chain map between bounded-below
complexes. The isomorphism itself is the explicitly constructed
`boundedComplexDirectImagePresheafIso`, so this assertion identifies the actual induced
maps, including restrictions, rather than asserting existence of unrelated isomorphisms.
Source: Stacks Tag 0D6I and the blueprint's first direct-image proof paragraph
(blueprint: lem-pe-bounded-complex-direct-image-presheaf).

Proof plan:
1. Modules over the arbitrary ring sheaf on the chosen small site are Grothendieck
   (lem-weil-pbc-ring-sheaves-grothendieck); transport its functorial K-injective
   replacement to the original site
   (lem-sfb-grothendieck-k-injective). The recorded right-derived unit computes direct
   image and each evaluation on this same replacement (def-sfb-right-derived-functor).
2. Base change gives sections I(u(V)), with its module action and restrictions
   (det-pe-topos-functoriality-inverse-image). Its sectionwise homology is precisely P.
3. Exact abelian sheafification commutes with homology
   (lem-weil-pbc-sheafification-exact, lem-weil-pbc-exact-functor-complex-cohomology).
   The counit identifies sheafifications of the sheaf terms with themselves
   (def-weil-pbc-sheafification); forgetting module structure is exact
   (lem-weil-pbc-module-sheaves-colimits-forgetful). These are the displayed iso's factors.
4. Every factor is natural in the lifted chain map. Any other K-injective representative
   gives the same comparison, since maps into it are unique up to homotopy
   (lem-weil-pbc-kinjective-hom-derived); additive evaluation preserves those homotopies.
   Naturality of the right-derived unit gives resolution independence and the equality. -/
theorem boundedComplexDirectImagePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (topology X) RingCat.{u + 1}) (q : ℤ)
    (K L : CochainComplex (ringedSiteModules.{u + 1} R) ℤ)
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.X n))
    (hL : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (L.X n)) (t : K ⟶ L) :
    (presheafToSheaf (topology Y) AddCommGrpCat.{u + 1}).map
        ((inverseImageCohomologyPresheaf f R q).map t) ≫
        (boundedComplexDirectImagePresheafIso f R q L hL).hom =
      (boundedComplexDirectImagePresheafIso f R q K hK).hom ≫
        ((DerivedCategory.Q ⋙ boundedRingHigherDirectImage f R q) ⋙
          SheafOfModules.toSheaf _).map t := by
  have h := (boundedComplexDirectImagePresheafNatIso f R q).hom.naturality t
  dsimp only [boundedComplexDirectImagePresheafNatIso,
    boundedComplexDirectImagePresheafIso, sectionHomologySheafificationNatIso,
    sectionHomologySheafificationIso, sectionHomologyPresheafNatIso,
    ringDirectImageResolutionNatIso, Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso, exactHomologyNatIso,
    Functor.associator, Iso.refl, Functor.mapHomologicalComplexIdIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Functor.comp_obj, Functor.comp_map, Functor.mapIso_hom, Functor.mapIso_inv,
    ] at h
  dsimp only [boundedComplexDirectImagePresheafIso, sectionHomologySheafificationIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc, Functor.comp_map, Iso.app_inv, Functor.mapIso_inv,
    sectionHomologyPresheafIso, Functor.comp_obj] at h ⊢
  convert h using 1 <;> congr 8

end AlgebraicGeometry.Scheme.ProEt
