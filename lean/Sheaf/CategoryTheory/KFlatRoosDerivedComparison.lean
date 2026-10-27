/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.CategoryTheory.KFlatAugmentedRoosDefinitions
public import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-! # Canonical comparison with the right derived tower limit

Source: Stacks derived.tex Tags 070I and 070Y and sites-cohomology.tex Tag 0941.
(blueprint: lem-sfb-kflat-roos-derived-comparison).

The ordinary-limit comparison is defined by its projections. Limits factor through
homotopy. Quasi-isomorphisms between K-injectives are homotopy equivalences, so the
K-injective derivability structure makes the derived-limit unit invertible there
and makes its derivation absolute. Its universal property constructs the comparison.
The universal unit equation gives its resolution formula and augmentation identity.
For naturality in another functor, first cancel the invertible unit on a K-injective
tower, check the ordinary-limit square by projections, and then transport the equality
along a K-injective resolution of an arbitrary tower. This proof does not require
preservation of injective objects by the functor on complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b w u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex
namespace CategoryTheory.KFlatAugmentedRoos
variable {M : Type a} [Category.{b} M] [Abelian M]
variable [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M]
  [HasDerivedCategory.{w} M] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ M)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def limitComparison (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ) :
    roosLimitFunctor ⋙ F ⟶ tower F ⋙ roosLimitFunctor where
  app X := limit.post X.asFunctor F
  naturality X Y f := by
    apply limit.hom_ext
    intro n
    change (F.map (limMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)) ≫
        limit.post Y.asFunctor F) ≫ limit.π (Y.asFunctor ⋙ F) n =
      (limit.post X.asFunctor F ≫ limMap (Functor.whiskerRight
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) F)) ≫
          limit.π (Y.asFunctor ⋙ F) n
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    erw [Category.assoc, limit.post_π, Category.assoc, limMap_π]
    rw [← Category.assoc, limit.post_π]
    rw [← F.map_comp, limMap_π, F.map_comp]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma limitComparison_π (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (n : ℕᵒᵖ) :
    (limitComparison F).app X ≫ limit.π ((tower F).obj X).asFunctor n =
      F.map (limit.π X.asFunctor n) := limit.post_π _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def limitComparisonMap (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (q : (tower F).obj I ⟶ J) :
    F.obj (limit I.asFunctor) ⟶ limit J.asFunctor :=
  (limitComparison F).app I ≫ roosLimitFunctor.map q

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma limitComparisonMap_π (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (q : (tower F).obj I ⟶ J) (n : ℕᵒᵖ) :
    limitComparisonMap F I J q ≫ limit.π J.asFunctor n =
      F.map (limit.π I.asFunctor n) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app n := by
  change ((limitComparison F).app I ≫
    limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q)) ≫
      limit.π J.asFunctor n = _
  dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
  erw [Category.assoc, limMap_π, ← Category.assoc]
  erw [limitComparison_π]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
def productComparisonMap (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (q : (tower F).obj I ⟶ J) :
    F.obj (roosP I) ⟶ roosP J :=
  Pi.lift (fun n ↦ F.map (Pi.π _ n) ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasLimitsOfShape ℕᵒᵖ M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma productComparisonMap_π (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (q : (tower F).obj I ⟶ J) (n : ℕ) :
    productComparisonMap F I J q ≫ Pi.π _ n =
      F.map (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (.op k)) n) ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (.op n) :=
  Pi.lift_π _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasLimitsOfShape ℕᵒᵖ M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma productComparisonMap_comm
    (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ) [F.Additive]
    (I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (q : (tower F).obj I ⟶ J) :
    F.map (roosU I) ≫ productComparisonMap F I J q =
      productComparisonMap F I J q ≫ roosU J := by
  apply Pi.hom_ext
  intro n
  simp only [roosU, towerTransitionEndomorphism, towerProductShift,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, Pi.lift_π,
    Functor.map_sub, Functor.map_id, Category.id_comp, Category.comp_id]
  rw [productComparisonMap_π]
  congr 1
  rw [← F.map_comp_assoc, Pi.lift_π, F.map_comp]
  erw [← Category.assoc, productComparisonMap_π]
  simp only [Category.assoc]
  erw [(HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).naturality]
  rfl


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] [HasLimitsOfShape ℕᵒᵖ M]
  [HasDerivedCategory M] [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
theorem tower_quasiIso
    (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (hF : ∀ (X Y : CochainComplex M ℤ) (f : X ⟶ Y), QuasiIso f → QuasiIso (F.map f))
    {X Y : CochainComplex (ℕᵒᵖ ⥤ M) ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso ((tower F).map f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  exact hF _ _
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app n)
    ((HomologicalComplex.quasiIso_iff_evaluation f).1 hf n)

omit [HasCountableProducts M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma roosBaseLimit_additive : (lim : (ℕᵒᵖ ⥤ M) ⥤ M).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

attribute [local instance] roosBaseLimit_additive

noncomputable def roosLimitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

noncomputable def roosLimitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) :
    IsLimit (roosLimitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

noncomputable def roosLimitModelPointIso (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (roosLimitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

omit [HasCountableProducts M] [HasDerivedCategory M]
  [HasDerivedCategory (ℕᵒᵖ ⥤ M)] in
lemma roosLimitModelPointIso_hom_π (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (n : ℕᵒᵖ) :
    (roosLimitModelPointIso I).hom ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  IsLimit.conePointUniqueUpToIso_hom_comp (roosLimitModelLimit I) (limit.isLimit I.asFunctor) n

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
noncomputable def roosLimitModelIso :
    (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor :=
  NatIso.ofComponents roosLimitModelPointIso (by
    intro X Y f
    dsimp only [roosLimitFunctor, Functor.comp_map,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    apply limit.hom_ext
    intro n
    change ((lim.mapHomologicalComplex (.up ℤ)).map f ≫
        (roosLimitModelPointIso Y).hom) ≫ limit.π Y.asFunctor n =
      ((roosLimitModelPointIso X).hom ≫
        limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)) ≫
          limit.π Y.asFunctor n
    simp only [Category.assoc]
    erw [roosLimitModelPointIso_hom_π, limMap_π, ← Category.assoc,
      roosLimitModelPointIso_hom_π]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

/-- Termwise limits on towers factor through the homotopy category. -/
def limitHomotopyIso : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ≅
    HomotopyCategory.quotient (ℕᵒᵖ ⥤ M) (.up ℤ) ⋙
      (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w} :=
  Functor.isoWhiskerRight roosLimitModelIso.symm _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso M).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
            Functor.associator _ _ _

variable [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ M)]

omit [HasCountableProducts M] [HasDerivedCategory (ℕᵒᵖ ⥤ M)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ M)] in
/-- The limit functor followed by localization is computed on K-injective towers. -/
theorem limit_derives : (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ M)).Derives
    (roosLimitFunctor ⋙ DerivedCategory.Q.{w} (C := M)) := by
  intro I J f hf
  have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
    (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
  let H := (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomotopyCategory (.up ℤ) ⋙
    DerivedCategory.Qh.{w}
  have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
    (CochainComplex.KInjectives.toHomotopyCategory.map f)
  have hmap' : IsIso ((HomotopyCategory.quotient _ _ ⋙ H).map f.hom) := hmap
  have heq : (roosLimitFunctor ⋙ DerivedCategory.Q.{w}).map f.hom =
      limitHomotopyIso.hom.app I.obj ≫
        (HomotopyCategory.quotient _ _ ⋙ H).map f.hom ≫
          limitHomotopyIso.inv.app J.obj := by
    rw [← limitHomotopyIso.hom.naturality_assoc]
    simp
  change IsIso ((roosLimitFunctor ⋙ DerivedCategory.Q.{w}).map f.hom)
  rw [heq]
  infer_instance

omit [HasCountableProducts M] in
/-- The derived-limit unit is invertible on K-injective towers. -/
theorem unit_isIso
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
    (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) [I.IsKInjective] : IsIso (η.app I) :=
  limit_derives.isIso_of_isRightDerivedFunctor η (CochainComplex.KInjectives.mk I)

section Universal
variable (F : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
  (T : DerivedCategory.{w} M ⥤ DerivedCategory.{w} M)
  (S : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ M))
  (e : DerivedCategory.Q.{w} ⋙ T ≅ F ⋙ DerivedCategory.Q.{w})
  (eS : DerivedCategory.Q.{w} ⋙ S ≅ tower F ⋙ DerivedCategory.Q.{w})
  (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} M)
  (η : roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)

def comparisonSourceUnit :
    (roosLimitFunctor ⋙ DerivedCategory.Q.{w}) ⋙ T ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ T) :=
  Functor.whiskerRight η T ≫ (Functor.associator _ _ _).hom

def comparisonTargetUnit :
    (roosLimitFunctor ⋙ DerivedCategory.Q.{w}) ⋙ T ⟶
      DerivedCategory.Q.{w} ⋙ (S ⋙ RF) :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft roosLimitFunctor e.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (limitComparison F) DerivedCategory.Q.{w} ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft (tower F) η ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eS.inv RF ≫
    (Functor.associator _ _ _).hom

omit [HasCountableProducts M] in
/-- The right derived limit remains derived after postcomposition by any functor. -/
theorem comparison_absolute
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))] :
    (RF ⋙ T).IsRightDerivedFunctor (comparisonSourceUnit T RF η)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ)) := by
  apply LocalizerMorphism.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure
    (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ M)) η
  intro I
  have := I.property
  exact unit_isIso RF η I.obj

variable [hAbs : (RF ⋙ T).IsRightDerivedFunctor (comparisonSourceUnit T RF η)
  (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]

def derivedComparison : RF ⋙ T ⟶ S ⋙ RF := by
  exact (RF ⋙ T).rightDerivedDesc (comparisonSourceUnit T RF η)
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ)) _
    (comparisonTargetUnit F T S e eS RF η)

def comparison : DerivedCategory.Q.{w} ⋙ RF ⋙ T ⟶
    tower F ⋙ DerivedCategory.Q.{w} ⋙ RF :=
  Functor.whiskerLeft DerivedCategory.Q (derivedComparison F T S e eS RF η) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight eS.hom RF ≫
    (Functor.associator _ _ _).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ M)] in
theorem comparison_fac (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) :
    T.map (η.app X) ≫ (comparison F T S e eS RF η).app X =
      e.hom.app (limit X.asFunctor) ≫
        DerivedCategory.Q.{w}.map ((limitComparison F).app X) ≫
          η.app ((tower F).obj X) := by
  have h := (RF ⋙ T).rightDerived_fac_app (comparisonSourceUnit T RF η)
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ)) _
    (comparisonTargetUnit F T S e eS RF η) X
  dsimp only [comparisonSourceUnit, comparisonTargetUnit, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at h
  simp only [Category.comp_id, Category.id_comp] at h
  change T.map (η.app X) ≫ (derivedComparison F T S e eS RF η).app _ = _ at h
  dsimp only [comparison, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.comp_id, Category.id_comp]
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← RF.map_comp, Iso.inv_hom_id_app,
    Functor.map_id]
  dsimp only [roosLimitFunctor, Functor.comp_obj,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
  simp only [Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ M)] in
theorem comparison_augmentation
    (X : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (γ : Cone X.asFunctor) :
    T.map (DerivedCategory.Q.{w}.map (limit.lift X.asFunctor γ) ≫ η.app X) ≫
        (comparison F T S e eS RF η).app X =
      e.hom.app γ.pt ≫ DerivedCategory.Q.{w}.map
        (limit.lift ((tower F).obj X).asFunctor (F.mapCone γ)) ≫
          η.app ((tower F).obj X) := by
  rw [Functor.map_comp, Category.assoc, comparison_fac F T S e eS RF η X]
  erw [← Category.assoc, ← Category.assoc, e.hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  change _ ≫ DerivedCategory.Q.map
    (F.map (limit.lift X.asFunctor γ) ≫ limit.post X.asFunctor F) ≫ _ = _
  rw [limit.lift_post]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] in
/-- The derived comparison is represented on every pair of tower resolutions by the
ordinary-limit comparison with its prescribed projections. -/
theorem comparison_resolution
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (hF : ∀ (X Y : CochainComplex M ℤ) (f : X ⟶ Y), QuasiIso f → QuasiIso (F.map f))
    (X I J : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) (s : X ⟶ I) (q : (tower F).obj I ⟶ J)
    [QuasiIso s] [I.IsKInjective] [QuasiIso q] [J.IsKInjective] :
    ∃ (dI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
        RF.obj (DerivedCategory.Q.{w}.obj X))
      (dJ : DerivedCategory.Q.{w}.obj (limit J.asFunctor) ≅
        RF.obj (DerivedCategory.Q.{w}.obj ((tower F).obj X))),
      dI.hom ≫ RF.map (DerivedCategory.Q.map s) = η.app I ∧
      dJ.hom ≫ RF.map (DerivedCategory.Q.map ((tower F).map s ≫ q)) = η.app J ∧
      (comparison F T S e eS RF η).app X =
        T.map dI.inv ≫ e.hom.app (limit I.asFunctor) ≫
          DerivedCategory.Q.map (limitComparisonMap F I J q) ≫ dJ.hom := by
  have := unit_isIso RF η I
  have := unit_isIso RF η J
  have := tower_quasiIso F hF s (inferInstance : QuasiIso s)
  let dI := asIso (η.app I) ≪≫ (RF.mapIso (asIso (DerivedCategory.Q.map s))).symm
  let dJ := asIso (η.app J) ≪≫
    (RF.mapIso (asIso (DerivedCategory.Q.map ((tower F).map s ≫ q)))).symm
  refine ⟨dI, dJ, ?_, ?_, ?_⟩
  · dsimp [dI]
    simp
  · dsimp [dJ]
    simp
  · have hdJ : dJ.hom ≫
        RF.map (DerivedCategory.Q.map ((tower F).map s ≫ q)) = η.app J := by
      dsimp [dJ]
      simp
    have hdI : dI.inv = RF.map (DerivedCategory.Q.map s) ≫ inv (η.app I) := rfl
    apply (cancel_mono (RF.map (DerivedCategory.Q.map ((tower F).map s ≫ q)))).1
    simp only [Category.assoc, hdJ, hdI, T.map_comp]
    rw [DerivedCategory.Q.map_comp, RF.map_comp]
    have hn := (comparison F T S e eS RF η).naturality s
    change T.map (RF.map (DerivedCategory.Q.map s)) ≫
        (comparison F T S e eS RF η).app I =
      (comparison F T S e eS RF η).app X ≫
        RF.map (DerivedCategory.Q.map ((tower F).map s)) at hn
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc]
    apply congrArg (T.map (RF.map (DerivedCategory.Q.map s)) ≫ ·)
    apply (cancel_epi (T.map (η.app I))).1
    rw [← Category.assoc, comparison_fac F T S e eS RF η I]
    simp only [← T.map_comp_assoc, IsIso.hom_inv_id, T.map_id, Category.id_comp]
    dsimp only [limitComparisonMap]
    rw [DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    congr 2
    exact (η.naturality q).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] in
theorem comparison_naturality_kinjective
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (G : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (T' : DerivedCategory.{w} M ⥤ DerivedCategory.{w} M)
    (S' : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ M))
    (e' : DerivedCategory.Q.{w} ⋙ T' ≅ G ⋙ DerivedCategory.Q.{w})
    (eS' : DerivedCategory.Q.{w} ⋙ S' ≅ tower G ⋙ DerivedCategory.Q.{w})
    [hAbs' : (RF ⋙ T').IsRightDerivedFunctor (comparisonSourceUnit T' RF η)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (τ : F ⟶ G) (μ : T ⟶ T')
    (hμ : ∀ U, μ.app (DerivedCategory.Q.obj U) ≫ e'.hom.app U =
      e.hom.app U ≫ DerivedCategory.Q.map (τ.app U))
    (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) [I.IsKInjective] :
    μ.app (RF.obj (DerivedCategory.Q.obj I)) ≫
        (comparison G T' S' e' eS' RF η).app I =
      (comparison F T S e eS RF η).app I ≫
        RF.map (DerivedCategory.Q.map ((towerMap τ).app I)) := by
  have := unit_isIso RF η I
  apply (cancel_epi (T.map (η.app I))).1
  erw [← Category.assoc, μ.naturality]
  simp only [Category.assoc]
  rw [comparison_fac G T' S' e' eS' RF η]
  erw [← Category.assoc, ← Category.assoc, hμ]
  simp only [Category.assoc]
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hlim : τ.app (limit I.asFunctor) ≫ (limitComparison G).app I =
      (limitComparison F).app I ≫ roosLimitFunctor.map ((towerMap τ).app I) := by
    apply limit.hom_ext
    intro n
    erw [Category.assoc, limitComparison_π]
    erw [← τ.naturality]
    change _ = ((limitComparison F).app I ≫
      limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((towerMap τ).app I))) ≫ limit.π ((tower G).obj I).asFunctor n
    erw [Category.assoc, limMap_π, ← Category.assoc, limitComparison_π]
    rfl
  erw [hlim, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  erw [η.naturality]
  have h := comparison_fac F T S e eS RF η I
  erw [← reassoc_of% h]
  simp only [Functor.comp_map]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [HasCountableProducts M] in
theorem comparison_naturality
    [RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (G : CochainComplex M ℤ ⥤ CochainComplex M ℤ)
    (T' : DerivedCategory.{w} M ⥤ DerivedCategory.{w} M)
    (S' : DerivedCategory.{w} (ℕᵒᵖ ⥤ M) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ M))
    (e' : DerivedCategory.Q.{w} ⋙ T' ≅ G ⋙ DerivedCategory.Q.{w})
    (eS' : DerivedCategory.Q.{w} ⋙ S' ≅ tower G ⋙ DerivedCategory.Q.{w})
    [hAbs' : (RF ⋙ T').IsRightDerivedFunctor (comparisonSourceUnit T' RF η)
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ M) (.up ℤ))]
    (τ : F ⟶ G) (μ : T ⟶ T')
    (hμ : ∀ U, μ.app (DerivedCategory.Q.obj U) ≫ e'.hom.app U =
      e.hom.app U ≫ DerivedCategory.Q.map (τ.app U))
    (hG : ∀ (X Y : CochainComplex M ℤ) (f : X ⟶ Y),
      QuasiIso f → QuasiIso (G.map f))
    (I : CochainComplex (ℕᵒᵖ ⥤ M) ℤ) :
    μ.app (RF.obj (DerivedCategory.Q.obj I)) ≫
        (comparison G T' S' e' eS' RF η).app I =
      (comparison F T S e eS RF η).app I ≫
        RF.map (DerivedCategory.Q.map ((towerMap τ).app I)) := by
  obtain ⟨N, hN, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective I
  let := hN
  let := hs
  have := tower_quasiIso G hG s hs
  apply (cancel_mono (RF.map (DerivedCategory.Q.map ((tower G).map s)))).1
  simp only [Category.assoc]
  erw [← (comparison G T' S' e' eS' RF η).naturality]
  erw [← Category.assoc, ← μ.naturality]
  simp only [Category.assoc]
  rw [comparison_naturality_kinjective F T S e eS RF η G T' S' e' eS' τ μ hμ N]
  erw [← Category.assoc, (comparison F T S e eS RF η).naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [← RF.map_comp, ← DerivedCategory.Q.map_comp,
    (towerMap τ).naturality, DerivedCategory.Q.map_comp, RF.map_comp]


end Universal

end CategoryTheory.KFlatAugmentedRoos
