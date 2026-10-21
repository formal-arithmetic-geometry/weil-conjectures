/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Algebra.Homology.Functor

import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerProperty
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover

/-!
# Continuous etale cohomology

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-prop-pe-continuous-cohomology-etale.md`; Bhatt--Scholze, Definition 5.6.1 and
Proposition 5.6.2 (blueprint: det-pe-continuous-cohomology-etale).

The continuous-sections complex is the termwise inverse limit of the section complexes.
Its right derived functor is specified by its universal property, without choosing a
resolution or a functorial cone in a triangulated category. Positive tower indices are
reindexed by `n + 1` throughout.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w u₁ u₂ v₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits Opposite

private lemma totalDerivedData {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (ek : K ≅ F.mapHomologicalComplex (.up ℤ)) :
    ∃ (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w₂} B)
      (η : K ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF),
      RF.IsRightDerivedFunctor η (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) := by
  let π := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let RF := F.rightDerivedFunctor
  let e₀ : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let e : K ⋙ DerivedCategory.Q ≅ π ⋙ H := Functor.isoWhiskerRight ek _ ≪≫ e₀
  let η : K ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
    e.hom ≫ Functor.whiskerLeft π F.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF).hom
  have hi (I : CochainComplex A ℤ) [I.IsKInjective] : IsIso (η.app I) := by
    dsimp [η]
    infer_instance
  refine ⟨RF, η, ?_, fun I hI ↦ hi I⟩
  have h : (CochainComplex.KInjectives.localizerMorphism A).Derives
      (K ⋙ DerivedCategory.Q) := by
    intro I J f hf
    have : IsIso (CochainComplex.KInjectives.toHomotopyCategory.map f) :=
      (CochainComplex.KInjectives.isIso_toHomotopyCategory_map_iff f).mpr hf
    have hmap := (HomotopyCategory.KInjectives.ι ⋙ H).map_isIso
      (CochainComplex.KInjectives.toHomotopyCategory.map f)
    have hmap' : IsIso ((π ⋙ H).map f.hom) := hmap
    have heq : (K ⋙ DerivedCategory.Q).map f.hom = e.hom.app I.obj ≫
          (π ⋙ H).map f.hom ≫ e.inv.app J.obj := by
      rw [← e.hom.naturality_assoc]
      simp
    change IsIso ((K ⋙ DerivedCategory.Q).map f.hom)
    rw [heq]
    infer_instance
  exact h.isRightDerivedFunctor_of_isIso η (fun I ↦ by
    have := I.property
    exact hi I.obj)


private noncomputable def complexDerivedUnit
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (G : A ⥤ B) [G.Additive] :
    G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
    Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (.up ℤ)) G.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) G.rightDerivedFunctor).hom

private theorem complexDerivedUnit_isIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    (G : A ⥤ B) [G.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit G).app I) := by
  dsimp [complexDerivedUnit]
  infer_instance


namespace AlgebraicGeometry.ProEtale

/-- Apply continuous sections to a complex of strict towers of etale abelian sheaves.
In degree `q` this is `lim_n Γ(X, I_n^q) = Γ(X, lim_n I_n^q)`; limits of sheaves and
complexes are computed sectionwise and degreewise, respectively. This is a real functor
on strict complexes, prior to deriving it.
Source: Bhatt--Scholze, Definition 5.6.1; Stacks, Tag 0940
(blueprint: det-pe-continuous-cohomology-etale). -/
noncomputable def continuousEtaleSectionComplexes (X : Scheme.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ ⥤
      CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
      (CochainComplex AddCommGrpCat.{u + 1} ℤ)).obj
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (ComplexShape.up ℤ)) ⋙ lim

attribute [local irreducible] continuousEtaleSectionComplexes

private theorem continuousTowerGrothendieck
    (A : Type*) [Category A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] :
    IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := by
  let G := separator A
  have hG := isSeparator_separator A
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun j : ℕᵒᵖ ↦ (evaluationLeftAdjoint A j).obj G) := by
    intro F F' f g hfg
    apply NatTrans.ext
    funext j
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight A j
    apply (adj.homEquiv G F').symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ j) ((adj.homEquiv G F).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  let : HasSeparator (ℕᵒᵖ ⥤ A) := ⟨_, hS.isSeparator_coproduct⟩
  let : HasFilteredColimitsOfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{u + 1, u + 1} (ℕᵒᵖ ⥤ A) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun P Q ↦ small_of_injective
    (f := fun f : P ⟶ Q ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

private theorem continuousLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ AddCommGrpCat.{u + 1}).Additive := by
  constructor
  intro F G f g
  apply limit.hom_ext
  intro n
  simp only [lim_map, limMap_π, Preadditive.add_comp, NatTrans.app_add,
    Preadditive.comp_add]

private noncomputable def continuousSectionIso (X : Scheme.{u}) :
    (((Functor.whiskeringRight ℕᵒᵖ
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) AddCommGrpCat.{u + 1}).obj
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙ lim).mapHomologicalComplex
          (.up ℤ)) ≅ continuousEtaleSectionComplexes X := by
  have := continuousLimitAdditive.{u}
  unfold continuousEtaleSectionComplexes
  let A := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let B := AddCommGrpCat.{u + 1}
  let G := Sheaf.Γ X.smallEtaleTopology B
  let W := (Functor.whiskeringRight ℕᵒᵖ A B).obj G
  let e : W.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
          (CochainComplex B ℤ)).obj (G.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
          (HomologicalComplex.functorEquivalence B (ComplexShape.up ℤ) ℕᵒᵖ).inverse :=
    Iso.refl _
  exact (Functor.mapHomologicalComplexCompIso (Iso.refl (W ⋙ lim)) (.up ℤ)).symm ≪≫
    Functor.isoWhiskerRight e _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
          (HomologicalComplex.functorEquivalenceInverseCompMapHomologicalComplexLim
            B (ComplexShape.up ℤ) ℕᵒᵖ))

private theorem continuousSectionPreservesKInjective (X : Scheme.{u}) :
    ((Functor.whiskeringRight ℕᵒᵖ
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) AddCommGrpCat.{u + 1}).obj
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})).PreservesKInjectiveComplexes := by
  let L := (Functor.whiskeringRight ℕᵒᵖ AddCommGrpCat.{u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).obj
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  have : PreservesFiniteLimits
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
    unfold constantSheaf
    infer_instance
  have : PreservesFiniteLimits L := by
    exact ⟨fun J _ _ ↦ preservesLimitsOfShape_of_evaluation L J
      (fun n ↦ inferInstance)⟩
  have : L.IsLeftAdjoint := (Adjunction.whiskerRight ℕᵒᵖ
    (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1})).isLeftAdjoint
  have : L.PreservesHomology := by infer_instance
  exact (Adjunction.whiskerRight ℕᵒᵖ
    (constantSheafΓAdj X.smallEtaleTopology AddCommGrpCat.{u + 1})).preservesKInjectiveComplexes

private structure ContinuousDerivedModel (X : Scheme.{u})
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] where
  Rc : DerivedCategory.{w}
    (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}
  η : continuousEtaleSectionComplexes X ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rc
  isRightDerived : Rc.IsRightDerivedFunctor η
    (HomologicalComplex.quasiIso
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (.up ℤ))
  isIso : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)

private theorem continuousDerivedData (X : Scheme.{u})
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Nonempty (ContinuousDerivedModel X) := by
  let A := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := continuousTowerGrothendieck A
  let H := (Functor.whiskeringRight ℕᵒᵖ A AddCommGrpCat.{u + 1}).obj
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⋙ lim
  have := continuousLimitAdditive.{u}
  obtain ⟨Rc, η, hRc, hI⟩ := totalDerivedData H
    (continuousEtaleSectionComplexes X) (continuousSectionIso X).symm
  exact ⟨⟨Rc, η, hRc, hI⟩⟩

private noncomputable def towerSequenceIso
    {D : Type*} [Category D] (H : ℕᵒᵖ ⥤ D) :
    H ≅ Functor.ofOpSequence (X := fun n : ℕ ↦ H.obj (op n))
      (fun n : ℕ ↦ H.map (homOfLE (Nat.le_succ n)).op) := by
  let e : H ⟶ Functor.ofOpSequence (X := fun n : ℕ ↦ H.obj (op n))
      (fun n : ℕ ↦ H.map (homOfLE (Nat.le_succ n)).op) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by intro n; simp)
  have : ∀ n : ℕᵒᵖ, IsIso (e.app n) := fun n ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso e := NatIso.isIso_of_isIso_app e
  exact asIso e

private theorem derivedLimit_of_iso
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {K : ℕ → D} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    {L M : D} (e : L ≅ M) (hM : IsDerivedLimit f M) : IsDerivedLimit f L := by
  obtain ⟨p, δ, h⟩ := hM
  refine ⟨e.hom ≫ p, δ ≫ (shiftFunctor D (1 : ℤ)).map e.inv, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (e.hom ≫ p) (towerTransitionEndomorphism f)
        (δ ≫ (shiftFunctor D (1 : ℤ)).map e.inv))
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f) δ)
      e (Iso.refl _) (Iso.refl _)
      (by simp)
      (by simp)
      (by simp))).mpr h

private theorem continuousEtaleModel
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₂} A]
    [Abelian.HasKInjectiveResolutions A]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
    [Abelian.HasKInjectiveResolutions B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [CountableAB4Star B] [EnoughInjectives B]
    (G : A ⥤ B) [G.Additive]
    (hG : ((Functor.whiskeringRight ℕᵒᵖ A B).obj G).PreservesKInjectiveComplexes)
    (hP : HasCountableProducts (DerivedCategory.{w₂} B))
    (Rc : DerivedCategory.{w}
      (ℕᵒᵖ ⥤ A) ⥤
        DerivedCategory.{w₂} B)
    (η : (HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (CochainComplex B ℤ)).obj (G.mapHomologicalComplex (.up ℤ)) ⋙ lim) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Rc)
    (hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (F : ℕᵒᵖ ⥤ A) :
    let := hP
    IsDerivedLimit
      (K := fun n : ℕ ↦
        G.rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n))))
      (fun n : ℕ ↦
        G.rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map (F.map (homOfLE (Nat.le_succ n)).op)))
      (Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let := hP
  let W := (Functor.whiskeringRight ℕᵒᵖ A B).obj G
  let : W.PreservesKInjectiveComplexes := hG
  let K := (HomologicalComplex.single _ (.up ℤ) 0).obj F
  obtain ⟨I, hI, i, hi⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  let := hI
  have : QuasiIso i := hi.2
  let J := (W.mapHomologicalComplex (.up ℤ)).obj I
  let C := HomologicalComplex.complexOfFunctorsToFunctorToComplex (T := ℕᵒᵖ)
    (V := A) (c := ComplexShape.up ℤ)
  let s : C.obj K ≅ F ⋙ CochainComplex.singleFunctor A 0 :=
    NatIso.ofComponents (fun n ↦
      (HomologicalComplex.singleMapHomologicalComplex
        ((evaluation ℕᵒᵖ A).obj n) (.up ℤ) 0).app F)
      (by
        intro n m f
        apply HomologicalComplex.hom_ext
        intro j
        by_cases h : j = 0
        · subst j
          simp only [HomologicalComplex.comp_f]
          dsimp [C, K, CochainComplex.singleFunctor, CochainComplex.singleFunctors,
            HomologicalComplex.singleMapHomologicalComplex,
            HomologicalComplex.complexOfFunctorsToFunctorToComplex,
            HomologicalComplex.asFunctor, HomologicalComplex.single]
          simp only [Category.comp_id, Category.id_comp]
          change F.map f ≫ 𝟙 (F.obj m) = 𝟙 (F.obj n) ≫ F.map f
          simp only [Category.comp_id, Category.id_comp]
        · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j h).eq_of_tgt _ _)
  let q : F ⋙ DerivedCategory.singleFunctor A 0 ≅ I.asFunctor ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ A 0) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight s.symm _ ≪≫
      (by
        have hn (n : ℕᵒᵖ) : IsIso
            ((Functor.whiskerRight (C.map i) DerivedCategory.Q).app n) := by
          change IsIso (DerivedCategory.Q.map
            ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map i))
          infer_instance
        have := NatIso.isIso_of_isIso_app
          (Functor.whiskerRight (C.map i) DerivedCategory.Q)
        exact asIso (Functor.whiskerRight (C.map i) DerivedCategory.Q))
  let a : J.asFunctor ⋙ DerivedCategory.Q ≅
      I.asFunctor ⋙ DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    NatIso.ofComponents (fun n ↦ by
      have := tower_evaluation_isKInjective A I n
      have := complexDerivedUnit_isIso G (I.asFunctor.obj n)
      exact asIso ((complexDerivedUnit G).app (I.asFunctor.obj n)))
      (by intro n m f; exact (complexDerivedUnit G).naturality (I.asFunctor.map f))
  let e := a ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight q.symm G.rightDerivedFunctor ≪≫
    towerSequenceIso (F ⋙ DerivedCategory.singleFunctor A 0 ⋙ G.rightDerivedFunctor)
  have hj := derivedCategory_towerLimit_property
    B hP (inferInstance : EnoughInjectives B)
    J _ _ e (limit.cone J.asFunctor) (limit.isLimit _)
  have : IsIso (η.app I) := hη I hI
  let E : Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Q.obj (limit J.asFunctor) :=
    Rc.mapIso (asIso (DerivedCategory.Q.map i)) ≪≫ (asIso (η.app I)).symm
  change IsDerivedLimit
    (K := fun n : ℕ ↦ (F ⋙ DerivedCategory.singleFunctor A 0 ⋙ G.rightDerivedFunctor).obj
      (op n))
    (fun n : ℕ ↦ (F ⋙ DerivedCategory.singleFunctor A 0 ⋙ G.rightDerivedFunctor).map
      (homOfLE (Nat.le_succ n)).op) _
  exact derivedLimit_of_iso _ E hj

private theorem abelianRoosSurjective
    {A : Type*} [Category A] [Preadditive A]
    (E : A ⥤ AddCommGrpCat.{u + 1}) [E.Additive]
    (F : ℕ → A) [HasProduct F]
    [PreservesLimit (Discrete.functor F) (E ⋙ forget _)]
    (t : ∀ n, F (n + 1) ⟶ F n)
    (ht : ∀ n, Function.Surjective (E.map (t n))) :
    Function.Surjective (E.map (towerTransitionEndomorphism t)) := by
  classical
  intro y
  choose σ hσ using ht
  let x : ∀ n, E.obj (F n) :=
    fun n ↦ Nat.rec (0 : E.obj (F 0))
      (fun n a ↦ σ n (a - E.map (Pi.π F n) y)) n
  let T := E ⋙ forget _
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves T (limit.isLimit (Discrete.functor F)))
  let s : (Discrete.functor F ⋙ T).sections :=
    ⟨fun j ↦ x j.as, by
      rintro ⟨i⟩ ⟨j⟩ a
      obtain rfl := Discrete.eq_of_hom a
      have ha : a = 𝟙 _ := Subsingleton.elim _ _
      subst a
      simp⟩
  refine ⟨e.symm s, ?_⟩
  apply e.injective
  apply Subtype.ext
  funext j
  have hx (n : ℕ) : E.map (Pi.π F n) (e.symm s) = x n :=
    congrArg (fun z ↦ z.val ⟨n⟩) (e.apply_symm_apply s)
  change E.map (Pi.π F j.as) (E.map (towerTransitionEndomorphism t) (e.symm s)) =
    E.map (Pi.π F j.as) y
  rw [← ConcreteCategory.comp_apply, ← E.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_π, E.map_sub, E.map_comp, AddCommGrpCat.hom_sub,
    AddMonoidHom.sub_apply, ConcreteCategory.comp_apply, hx]
  change x j.as - E.map (t j.as) (x (j.as + 1)) = _
  rw [show x (j.as + 1) = σ j.as (x j.as - E.map (Pi.π F j.as) y) from rfl, hσ]
  exact sub_sub_cancel _ _

private theorem proEtaleAbelianRoosEpi (X : Scheme.{u})
    (F : ℕ → Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (t : ∀ n, F (n + 1) ⟶ F n) (ht : ∀ n, Epi (t n)) :
    Epi (towerTransitionEndomorphism t) := by
  let J := Scheme.ProEt.topology X
  let T := sheafCompose J (forget AddCommGrpCat.{u + 1})
  have hlocal (n : ℕ) : Sheaf.IsLocallySurjective (T.map (t n)) := by
    have : Epi (t n) := ht n
    have : Sheaf.IsLocallySurjective (t n) :=
      (Sheaf.isLocallySurjective_iff_epi' _ (t n)).mpr inferInstance
    infer_instance
  have h : Sheaf.IsLocallySurjective (T.map (towerTransitionEndomorphism t)) := by
    constructor
    intro U s
    obtain ⟨K, V, a, hcov, _, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X U
    apply J.superset_covering (S := Sieve.ofArrows V a) _
      (Precoverage.generate_mem_toGrothendieck hcov)
    apply (Sieve.generate_le_iff _ _).mpr
    intro W g hg
    obtain ⟨k⟩ := hg
    let E := (sheafSections J AddCommGrpCat.{u + 1}).obj (op (V k))
    have : E.Additive := ⟨by intros; rfl⟩
    have : PreservesLimit (Discrete.functor F) (E ⋙ forget _) := by
      change PreservesLimit (Discrete.functor F)
        ((sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙
          (evaluation _ _).obj (op (V k))) ⋙ forget _)
      infer_instance
    have hs (n : ℕ) : Function.Surjective (E.map (t n)) := by
      exact hweak k _ _ (T.map (t n)) inferInstance
    exact abelianRoosSurjective E F t hs
      ((T.obj (∏ᶜ F)).obj.map (a k).op s)
  apply (Sheaf.isLocallySurjective_iff_epi' _ _).mp
  change Presheaf.IsLocallySurjective J (towerTransitionEndomorphism t).hom
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr h

private theorem singlePreservesCountableProduct
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    [HasCountableProducts A] [CountableAB4Star A] (F : ℕ → A) :
    PreservesLimit (Discrete.functor F) (DerivedCategory.singleFunctor.{w} A 0) := by
  have : HasLimitsOfShape (Discrete ℕ) A := inferInstance
  have : HasExactLimitsOfShape (Discrete ℕ) A := inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := A)) :=
    inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) (CochainComplex.singleFunctor A 0) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.single A (.up ℤ) 0))
  exact (preservesLimit_iff_of_natIso (Discrete.functor F)
    (DerivedCategory.singleFunctorIsoCompQ A 0)).mpr inferInstance

private theorem abelianTowerModel
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [Abelian.HasKInjectiveResolutions A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A] [CountableAB4Star A]
    (hRoos : ∀ (K : ℕ → A) (f : ∀ n, K (n + 1) ⟶ K n),
      (∀ n, Epi (f n)) → Epi (towerTransitionEndomorphism f))
    (F : ℕᵒᵖ ⥤ A)
    (ht : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    Pretriangulated.IsHomotopyLimit
      ((DerivedCategory.singleFunctor A 0).mapCone (limit.cone F)) := by
  let K := fun n : ℕ ↦ F.obj (op n)
  let f := fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op
  let P : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hP : IsLimit P := productIsProduct K
  let t : P.pt ⟶ P.pt := Pi.lift (fun n ↦ Pi.π K (n + 1) ≫ f n)
  have htm (n : ℕ) : t ≫ P.proj n = P.proj (n + 1) ≫ f n := Pi.lift_π _ _
  let i : limit F ⟶ P.pt := Fan.IsLimit.lift hP (fun n ↦ limit.π F (op n))
  have hz : i ≫ (𝟙 P.pt - t) = 0 :=
    Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t htm (limit.cone F)
  let sc := ShortComplex.mk i (𝟙 P.pt - t) hz
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hP t htm (limit.isLimit F)
  have hm : Mono i := mono_of_isLimit_fork hk
  have he : Epi (𝟙 P.pt - t) := hRoos K f ht
  have hSES : sc.ShortExact :=
    ShortComplex.ShortExact.mk' (sc.exact_of_f_is_kernel hk) hm he
  let S := DerivedCategory.singleFunctor A 0
  have : PreservesLimit (Discrete.functor K) S := singlePreservesCountableProduct K
  let hSP := isLimitFanMkObjOfIsLimit S K P.proj hP
  have hSL : Pretriangulated.IsHomotopyLimit (S.mapCone (limit.cone F)) := by
    refine ⟨_, hSP, hSES.singleδ, ?_⟩
    have h₁ : Fan.IsLimit.lift hSP
        (fun n ↦ (S.mapCone (limit.cone F)).π.app (op n)) = S.map i := by
      apply Fan.IsLimit.hom_ext hSP
      intro n
      rw [Fan.IsLimit.fac]
      change S.map (limit.π F (op n)) = S.map i ≫ S.map (P.proj n)
      rw [← S.map_comp, Fan.IsLimit.fac]
    have h₂ : Pretriangulated.towerShift (F := F ⋙ S) hSP = S.map t := by
      apply Fan.IsLimit.hom_ext hSP
      intro n
      rw [Pretriangulated.towerShift, Fan.IsLimit.fac]
      change S.map (P.proj (n + 1)) ≫ S.map (f n) = S.map t ≫ S.map (P.proj n)
      rw [← S.map_comp, ← S.map_comp, htm]
    rw [h₁, h₂]
    change Pretriangulated.Triangle.mk (S.map i)
      (𝟙 (S.obj P.pt) - S.map t) hSES.singleδ ∈ _
    rw [← S.map_id, ← S.map_sub]
    exact hSES.singleTriangle_distinguished
  exact hSL

private theorem proEtaleAbelianModel (X : Scheme.{u})
    (F : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (ht : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) :
    Pretriangulated.IsHomotopyLimit
      (((DerivedCategory.singleFunctor _ 0) ⋙
        (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor).mapCone
          (limit.cone F)) := by
  let A := Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}
  let B := AddCommGrpCat.{u + 1}
  have : CountableAB4Star A := CountableAB4Star.of_epi_π_app_zero
    (Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat (S := X))
  have hSL := abelianTowerModel (proEtaleAbelianRoosEpi X) F ht
  let G := Sheaf.Γ (Scheme.ProEt.topology X) B
  have : PreservesFiniteLimits (constantSheaf (Scheme.ProEt.topology X) B) := by
    unfold constantSheaf
    infer_instance
  have : G.rightDerivedFunctor.IsRightAdjoint :=
    (constantSheafΓAdj (Scheme.ProEt.topology X) B).mapDerivedCategoryRightDerivedAdjunction
      |>.isRightAdjoint
  exact hSL.map G.rightDerivedFunctor

private theorem homotopyLimit_isDerivedLimit
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (c : Cone F) (hc : Pretriangulated.IsHomotopyLimit c) :
    IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) c.pt := by
  obtain ⟨P, hP, δ, h⟩ := hc
  let e : P.pt ≅ ∏ᶜ (fun n : ℕ ↦ F.obj (op n)) :=
    hP.conePointUniqueUpToIso (productIsProduct (fun n : ℕ ↦ F.obj (op n)))
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = P.proj n :=
    hP.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
  have ht : (𝟙 P.pt - Pretriangulated.towerShift hP) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) := by
    rw [towerTransitionEndomorphism, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.id_comp, Category.comp_id]
    congr 1
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, Pretriangulated.towerShift,
      Fan.IsLimit.fac, towerProductShift, Pi.lift_π]
    rw [← Category.assoc, he]
  refine ⟨Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ e.hom, e.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk _ (𝟙 P.pt - Pretriangulated.towerShift hP) δ)
      (Pretriangulated.Triangle.mk _ _ (e.inv ≫ δ)) (Iso.refl _) e e
      (by change (Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n))) ≫ e.hom =
            𝟙 _ ≫ ((Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n))) ≫ e.hom)
          simp only [Category.id_comp]) ht
      (by simp))).mp h

private noncomputable def whiskeredAdjunctionComparison
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (S : C ⥤ D) (U : C ⥤ E) (Df : D ⥤ E) (R : E ⥤ D)
    (Ge : D ⥤ H) (Gp : E ⥤ H) (adj : Df ⊣ R)
    (hunit : ∀ F, IsIso (adj.unit.app (S.obj F)))
    (eSD : S ⋙ Df ≅ U) (eRG : R ⋙ Ge ≅ Gp) : S ⋙ Ge ≅ U ⋙ Gp := by
  let e : S ≅ S ⋙ Df ⋙ R :=
    NatIso.ofComponents (fun F ↦ by
      have := hunit F
      exact asIso (adj.unit.app (S.obj F)))
      (by intro X Y f; exact adj.unit.naturality (S.map f))
  exact Functor.isoWhiskerRight e Ge ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Df eRG) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eSD Gp

private noncomputable def sectionsComparison (X : Scheme.{u}) :
    DerivedCategory.singleFunctor _ 0 ⋙
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor ≅
    comparisonUpperStar AddCommGrpCat.{u + 1} X ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor := by
  let A := AddCommGrpCat.{u + 1}
  let S := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0
  let U := comparisonUpperStar A X
  let D := U.mapDerivedCategory
  let R := (comparisonLowerStar A X).rightDerivedFunctor
  let Ge := (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctor
  let Gp := (Sheaf.Γ (Scheme.ProEt.topology X) A).rightDerivedFunctor
  let adj := derivedComparisonAdjunction A X
  have hunit (F : Sheaf X.smallEtaleTopology A) : IsIso (adj.unit.app (S.obj F)) :=
    isIso_derivedComparisonAdjunction_unit_app A X (S.obj F)
      ⟨0, inferInstance⟩
  exact whiskeredAdjunctionComparison S (U ⋙ DerivedCategory.singleFunctor _ 0)
    D R Ge Gp adj hunit (U.mapDerivedCategorySingleFunctor 0)
    (comparisonLowerStarCompRightDerivedGlobalSectionsIso A X) ≪≫
      Functor.associator _ _ _



private theorem isDerivedLimit_of_towerIso
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : ℕᵒᵖ ⥤ D) (e : F ≅ G)
    [HasCountableProducts D]
    (L : D)
    (hL : IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) L) :
    IsDerivedLimit (K := fun n : ℕ ↦ G.obj (op n))
      (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) L := by
  obtain ⟨p, δ, h⟩ := hL
  let E := Pi.mapIso (fun n : ℕ ↦ e.app (op n))
  have hE : E.hom ≫ towerTransitionEndomorphism
        (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) =
      towerTransitionEndomorphism
        (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) ≫ E.hom := by
    exact towerTransitionEndomorphism_natural_backward _ _
      (fun n ↦ (e.app (op n)).hom)
      (fun n ↦ (e.hom.naturality (homOfLE (Nat.le_succ n)).op).symm)
  refine ⟨p ≫ E.hom, E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk p _ δ)
      (Pretriangulated.Triangle.mk (p ≫ E.hom) _ (E.inv ≫ δ))
      (Iso.refl _) E E
      (by change p ≫ E.hom = 𝟙 _ ≫ (p ≫ E.hom); simp only [Category.id_comp])
      hE.symm
      (by simp))).mp h

private theorem continuousEtaleModelForSheaves (X : Scheme.{u})
    [CountableAB4Star AddCommGrpCat.{u + 1}]
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hP : HasCountableProducts (DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}))
    (D : ContinuousDerivedModel X)
    (F : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let := hP
    IsDerivedLimit
      (K := fun n : ℕ ↦
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n))))
      (fun n : ℕ ↦
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map (F.map (homOfLE (Nat.le_succ n)).op)))
      (D.Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let A := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) := continuousTowerGrothendieck A
  have hη := D.isIso
  let η := D.η
  unfold continuousEtaleSectionComplexes at η hη
  exact continuousEtaleModel.{w, u + 2, u + 2, u + 1, u + 1, u + 1}
    (A := A) (B := AddCommGrpCat.{u + 1})
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (continuousSectionPreservesKInjective X) hP D.Rc η hη F

private theorem twoDerivedLimitObjects
    {E : Type*} [Category E] [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E] [IsTriangulated E]
    [HasCountableProducts E]
    (F G : ℕᵒᵖ ⥤ E) (e : F ≅ G) (L M : E)
    (hL : IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
      (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) L)
    (hM : IsDerivedLimit (K := fun n : ℕ ↦ G.obj (op n))
      (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) M) :
    ∃ L₁ L₂ : E,
      IsDerivedLimit (K := fun n : ℕ ↦ F.obj (op n))
        (fun n : ℕ ↦ F.map (homOfLE (Nat.le_succ n)).op) L₁ ∧
      IsDerivedLimit (K := fun n : ℕ ↦ G.obj (op n))
        (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op) L₂ ∧
      Nonempty (L ≅ L₁) ∧ Nonempty (L₁ ≅ L₂) ∧ Nonempty (L₂ ≅ M) := by
  have hL' := isDerivedLimit_of_towerIso F G e L hL
  have he := (exists_isDerivedLimit_and_iso
    (fun n : ℕ ↦ G.obj (op n))
    (fun n : ℕ ↦ G.map (homOfLE (Nat.le_succ n)).op)).2 L M hL' hM
  exact ⟨L, M, hL, hM, ⟨Iso.refl _⟩, he, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.style.haveILetI false

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions

/-- The three isomorphisms identifying continuous etale cohomology. The functor `Rc`
and its unit are a total right derived functor of continuous sections, specified by
`IsRightDerivedFunctor`. The two middle objects are derived limits in the precise
Roos-triangle sense, with the original transitions, rather than unspecified cones.
Source: blueprint main-20261015, `sk-prop-pe-continuous-cohomology-etale.md`;
Bhatt--Scholze, Definition 5.6.1 and Proposition 5.6.2
(blueprint: det-pe-continuous-cohomology-etale).

Proof:
1. Realize towers as sheaves on the product of the small etale site with the ordered
positive integers (covers have constant index). Bounded-below injective resolutions
on this site give injective tower resolutions; exactness and evaluation are levelwise
(lem-weil-tower-category-levelwise-abelian, lem-sc-bounded-below-injective-resolution).
2. Levelwise sections have the exact left adjoint of levelwise constant sheaves, hence
preserve injectives (lem-sp-right-adjoint-preserves-injectives). Sections commute with
limits of sheaves. Thus continuous sections equal inverse limit of levelwise sections.
3. Evaluation has the exact finite-prefix left adjoint, so an injective tower resolution
is an injective resolution at every level. Apply lem-weil-pbc-right-derived-plus-injective
naturally in transitions to obtain a strict model for the derived section tower.
4. Applying continuous sections to this resolution and applying derived inverse limit
of its section tower give the same complex. The punctual integer-coefficient case of
lem-weil-pbc-ringed-strict-tower-homotopy-limit identifies it with a Roos derived limit.
Resolution comparison gives the right-derived universal property, also on unbounded
complexes by K-injective tower resolutions on the same small tower site.
5. Exact comparison inverse image transports the tower and its epimorphic transitions
(lem-pe-constant-left-module-inverse-image, with integer coefficients).
6. Resolve the pulled-back tower complex injectively on the pro-etale tower site. The
ordinary comparison unit followed by this resolution gives a strict map of section
towers. Each component is a quasi-isomorphism by sk-prop-sf-comparison with integer
coefficients and the injective computation of lem-weil-pbc-right-derived-plus-injective.
7. Derived inverse limit carries this strict quasi-isomorphism to an isomorphism.
By lem-weil-strict-roos-comparison and exact products of abelian groups the comparison
is represented by the map of strict Roos cones, so it uses the specified transitions.
8. Apply det-pe-continuous-cohomology-limit at the terminal pro-etale object: the pulled
back tower has epimorphic transitions. Its derived section limit is isomorphic to
derived sections of its ordinary limit. Uniqueness up to isomorphism of derived limits
(lem-weil-derived-limit-existence) supplies the final displayed isomorphism. -/
theorem continuousEtaleCohomology (X : Scheme.{u})
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] :
    ∃ (_hproducts : HasCountableProducts (DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}))
      (Rc : DerivedCategory.{w}
        (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory.{u + 1} AddCommGrpCat.{u + 1})
      (η : continuousEtaleSectionComplexes X ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ Rc),
      Rc.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso
          (ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ)) ∧
      ∀ (F : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        (∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)) →
        ∃ (L₁ L₂ : DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}),
          IsDerivedLimit
            (K := fun n : ℕ ↦
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj (F.obj (op n))))
            (fun n : ℕ ↦
              (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
                ((DerivedCategory.singleFunctor _ 0).map
                  (F.map (homOfLE (Nat.le_succ n)).op))) L₁ ∧
          IsDerivedLimit
            (K := fun n : ℕ ↦
              (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
                ((DerivedCategory.singleFunctor _ 0).obj
                  ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj (F.obj (op n)))))
            (fun n : ℕ ↦
              (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
                ((DerivedCategory.singleFunctor _ 0).map
                  ((comparisonUpperStar AddCommGrpCat.{u + 1} X).map
                    (F.map (homOfLE (Nat.le_succ n)).op)))) L₂ ∧
          Nonempty (Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅ L₁) ∧
          Nonempty (L₁ ≅ L₂) ∧
          Nonempty (L₂ ≅
            (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj
                (limit (F ⋙ comparisonUpperStar AddCommGrpCat.{u + 1} X)))) := by
  letI : HasDerivedCategory.{u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  letI : HasDerivedCategory.{u + 1}
      (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) := inferInstance
  letI : HasDerivedCategory.{u + 1} AddCommGrpCat.{u + 1} := inferInstance
  have : CountableAB4Star AddCommGrpCat.{u + 1} := by
    have : AB4StarOfSize.{0} AddCommGrpCat.{u + 1} :=
      AB4StarOfSize_shrink.{0, u + 1} AddCommGrpCat.{u + 1}
    infer_instance
  have hP : HasCountableProducts (DerivedCategory.{u + 1} AddCommGrpCat.{u + 1}) :=
    derivedCategory_hasCountableProducts AddCommGrpCat.{u + 1}
  let := hP
  let D := Classical.choice (continuousDerivedData X)
  refine ⟨hP, D.Rc, D.η, D.isRightDerived, ?_⟩
  intro F ht
  let U := comparisonUpperStar AddCommGrpCat.{u + 1} X
  let Gp := (Sheaf.Γ (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).rightDerivedFunctor
  let T₁ := F ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor
  let T₂ := F ⋙ U ⋙ DerivedCategory.singleFunctor _ 0 ⋙ Gp
  let L₁ := D.Rc.obj ((DerivedCategory.singleFunctor _ 0).obj F)
  let L₂ := Gp.obj ((DerivedCategory.singleFunctor _ 0).obj (limit (F ⋙ U)))
  have h₁ := continuousEtaleModelForSheaves X hP D F
  have h₂ : IsDerivedLimit (K := fun n : ℕ ↦ T₂.obj (op n))
      (fun n : ℕ ↦ T₂.map (homOfLE (Nat.le_succ n)).op) L₂ := by
    have ht' (n : ℕ) : Epi ((F ⋙ U).map (homOfLE (Nat.le_succ n)).op) := by
      have := ht n
      exact U.map_epi _
    exact homotopyLimit_isDerivedLimit T₂ _ (proEtaleAbelianModel X (F ⋙ U) ht')
  exact twoDerivedLimitObjects T₁ T₂
    (Functor.isoWhiskerLeft F (sectionsComparison X)) L₁ L₂ h₁ h₂

end AlgebraicGeometry.ProEtale
