/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Unbounded sections and localization of a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6F and its K-injective proof
(blueprint: lem-sfb-unbounded-sections-localization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.UnboundedSectionsLocalization

private lemma compUnit_app
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    (X : HomotopyCategory A (.up ℤ)) :
    (Functor.rightDerivedFunctorCompUnit F G).app X =
      G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj X) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app X) := by
  have hi := (Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).inv_hom_id_app X
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [Functor.rightDerivedFunctorCompUnit, hi]

private lemma compIso_objQ
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] (I : CochainComplex A ℤ) [I.IsKInjective] :
    (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Q.obj I) ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorObjQIso I).hom ≫
        (G.rightDerivedFunctorObjQIso
          ((F.mapHomologicalComplex (.up ℤ)).obj I)).hom =
      ((F ⋙ G).rightDerivedFunctorObjQIso I).hom := by
  have h := Functor.rightDerivedNatTrans_app
    (F ⋙ G).rightDerivedFunctor (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso _ (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient _ _).obj I)
  simp only [NatTrans.id_app, Category.id_comp] at h
  change (F ⋙ G).rightDerivedFunctorUnit.app _ ≫
    (F.rightDerivedFunctorCompIso G).hom.app _ = _ at h
  rw [compUnit_app] at h
  have hG : IsIso (G.rightDerivedFunctorUnit.app
      ((F.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj I))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I))))
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_inv, asIso_inv,
    Functor.map_comp, Category.assoc]
  simp only [Iso.app_hom]
  rw [← G.rightDerivedFunctor.map_comp_assoc
    ((DerivedCategory.quotientCompQhIso _).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I))
    ((DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)),
    Iso.hom_inv_id_app, G.rightDerivedFunctor.map_id, Category.id_comp]
  have hc : (F.rightDerivedFunctorCompIso G).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ _).obj I)) ≫
      G.rightDerivedFunctor.map (inv (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I))) ≫
      inv (G.rightDerivedFunctorUnit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ _).obj I))) =
      inv ((F ⋙ G).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj I)) := by
    rw [← cancel_epi ((F ⋙ G).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I)), ← Category.assoc, ← Category.assoc, h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.hom_inv_id,
      Functor.map_id, Category.id_comp]
  have hn := (F.rightDerivedFunctorCompIso G).hom.naturality
    ((DerivedCategory.quotientCompQhIso A).inv.app I)
  change (F ⋙ G).rightDerivedFunctor.map _ ≫ (F.rightDerivedFunctorCompIso G).hom.app _ =
    (F.rightDerivedFunctorCompIso G).hom.app _ ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctor.map _) at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% hc]
  rfl

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- The common-universe module category is Grothendieck abelian by the proved
small-site ring-sheaf theorem. Source: Stacks, Section 07A5
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance modulesGrothendieck : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  SheafOfModules.isGrothendieckAbelian R

/-- Evaluation at an object, followed by forgetting scalars.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev evaluation (W : C) : ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op W) ⋙
    forget₂ (ModuleCat.{u} (R.obj.obj (op W))) AddCommGrpCat.{u}

/-- Restriction is additive sectionwise.
Source: Stacks, Tags 03DJ and 08FI
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictionAdditive (W : C) : (SheafOfModules.overFunctor.{u} R W).Additive := by
  constructor
  intro M N f g
  ext V x
  rfl

/-- Termwise restriction of an unbounded complex.
Source: Stacks, Tag 0D6F (blueprint: lem-sfb-unbounded-sections-localization). -/
abbrev restrictComplex (W : C) :=
  (SheafOfModules.overFunctor.{u} R W).mapHomologicalComplex (.up ℤ)

/-- The restricted complex is K-injective by the recorded Tag 08FI theorem.
Source: Stacks, Tags 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
instance restrictedKInjective (W : C) (I : CochainComplex (ringedSiteModules.{u} R) ℤ)
    [I.IsKInjective] : CochainComplex.IsKInjective ((restrictComplex R W).obj I) :=
  isKInjective_restrict_localized R W inferInstance I

/-- The literal degreewise identity of the two evaluated complexes, including differentials.
Source: Stacks, Tag 0D6F, displayed equality in the proof
(blueprint: lem-sfb-unbounded-sections-localization). -/
def sectionComplexIdentity (W : C) (I : CochainComplex (ringedSiteModules.{u} R) ℤ) :
    ((evaluation R W).mapHomologicalComplex (.up ℤ)).obj I ≅
      ((evaluation (R.over W) (Over.mk (𝟙 W))).mapHomologicalComplex (.up ℤ)).obj
        ((restrictComplex R W).obj I) :=
  Iso.refl _

variable [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
  [HasDerivedCategory.{z} AddCommGrpCat.{u}]

/-- Unbounded derived evaluation, with scalars forgotten after evaluation.
Source: Stacks, Section 07A5 and Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedEvaluation (W : C) :
    DerivedCategory (ringedSiteModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (evaluation R W).rightDerivedFunctor

/-- Unbounded derived restriction. Since sectionwise restriction is exact, its total
right derived functor is the usual termwise restriction on the derived category.
Source: Stacks, Tags 03DJ, 08FI and 0D6F
(blueprint: lem-sfb-unbounded-sections-localization). -/
def derivedRestriction (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    DerivedCategory (ringedSiteModules.{u} R) ⥤
      DerivedCategory (ringedSiteModules.{u} (R.over W)) :=
  (SheafOfModules.overFunctor.{u} R W).rightDerivedFunctor

/-- Derived evaluation agrees naturally with derived evaluation on the localized site.
The comparison is normalized on every K-injective representative by the literal identity
of section complexes; its cohomology is an isomorphism in every integer degree.

Source: Stacks Project, Tag 0D6F
(blueprint: lem-sfb-unbounded-sections-localization).

Proof: (1) The module categories on the site and its slice are Grothendieck abelian,
so the existing general instance supplies K-injective resolutions. Restriction is
additive sectionwise and preserves K-injectives by Tag 08FI. The existing unbounded
composition theorem gives the natural comparison between derived evaluation and
restriction followed by localized derived evaluation.
(2) Evaluating a restricted complex at id_W is literally I(W), with the same
differentials. The defining universal-unit equation of the composition comparison,
evaluated on a K-injective I, identifies its component with the composite of the two
derived-unit inverses. Naturality along quotientCompQhIso and cancellation of the
intermediate quotient comparison give exactly sectionComplexIdentity.
(3) Apply the cohomology functor in each integer degree to the component isomorphism.
No truncation or boundedness is used. -/
theorem unboundedSectionsLocalization (W : C)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (R.over W))] :
    ∃ e : derivedEvaluation R W ≅
        derivedRestriction R W ⋙ derivedEvaluation (R.over W) (Over.mk (𝟙 W)),
      (∀ (I : CochainComplex (ringedSiteModules.{u} R) ℤ) [I.IsKInjective],
        e.hom.app (DerivedCategory.Q.obj I) ≫
          (derivedEvaluation (R.over W) (Over.mk (𝟙 W))).map
            ((SheafOfModules.overFunctor.{u} R W).rightDerivedFunctorObjQIso I).hom ≫
          ((evaluation (R.over W) (Over.mk (𝟙 W))).rightDerivedFunctorObjQIso
            ((restrictComplex R W).obj I)).hom =
        ((evaluation R W).rightDerivedFunctorObjQIso I).hom ≫
          DerivedCategory.Q.map (sectionComplexIdentity R W I).hom) ∧
      (∀ (K : DerivedCategory (ringedSiteModules.{u} R)) (q : ℤ),
        Nonempty
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
              ((derivedEvaluation R W).obj K) ≅
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
              ((derivedEvaluation (R.over W) (Over.mk (𝟙 W))).obj
                ((derivedRestriction R W).obj K)))) := by
  let F := SheafOfModules.overFunctor.{u} R W
  let G := evaluation (R.over W) (Over.mk (𝟙 W))
  let : F.PreservesKInjectiveComplexes :=
    ⟨fun I _ ↦ restrictedKInjective R W I⟩
  let e : derivedEvaluation R W ≅ derivedRestriction R W ⋙
      derivedEvaluation (R.over W) (Over.mk (𝟙 W)) :=
    F.rightDerivedFunctorCompIso G
  refine ⟨e, ?_, ?_⟩
  · intro I hI
    simp only [sectionComplexIdentity, Iso.refl_hom, Functor.map_id, Category.comp_id]
    exact compIso_objQ F G I
  · intro K q
    exact ⟨(DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).mapIso (e.app K)⟩

end CategoryTheory.UnboundedSectionsLocalization
