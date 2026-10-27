/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Sheaf.Paper.OrdinaryPullbackEvaluationCalculus

/-! # Ordinary evaluation of the normalized pullback compositor

Source: Stacks Project, sites-modules.tex, Tag 03D8; the finite normalization
in steps 1 and 3 of lem-pur-normalized-pullback-composition-transport.
(blueprint: lem-pur-ordinary-pullback-composition-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
namespace WeilConjectures.PullbackCompositionTransport

private theorem invertSquare
    {C : Type*} [Category C] {A B D E F : C}
    (p : A ≅ B) (q : D ≅ E) (r : E ≅ F) (a : A ⟶ D) (b : B ⟶ F)
    (h : a ≫ q.hom ≫ r.hom = p.hom ≫ b) :
    p.inv ≫ a = b ≫ r.inv ≫ q.inv := by
  apply (cancel_mono (q.hom ≫ r.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  exact p.inv_hom_id_assoc b

private theorem evaluationUnit_congr
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    (R R' : D ⥤ C) [R.IsRightAdjoint] [R'.IsRightAdjoint] (e : R = R')
    (E : C ⥤ c) (F : D ⥤ d) (l : c ⥤ d) (r : d ⥤ c)
    (η : 𝟭 c ⟶ l ⋙ r)
    (q : R.leftAdjoint ⋙ F ≅ E ⋙ l) (q' : R'.leftAdjoint ⋙ F ≅ E ⋙ l)
    (p : R ⋙ E ≅ F ⋙ r) (p' : R' ⋙ E ≅ F ⋙ r)
    (hq : HEq q q') (hp : HEq p p')
    (hu : ∀ M, E.map ((Adjunction.ofIsRightAdjoint R).unit.app M) ≫
      p.hom.app (R.leftAdjoint.obj M) ≫ r.map (q.hom.app M) = η.app (E.obj M)) :
    ∀ M, E.map ((Adjunction.ofIsRightAdjoint R').unit.app M) ≫
      p'.hom.app (R'.leftAdjoint.obj M) ≫ r.map (q'.hom.app M) = η.app (E.obj M) := by
  subst R'
  cases hq
  cases hp
  exact hu

private theorem eqToIso_heq {C : Type*} [Category C] {X X' Y : C}
    (e : X = X') (h : X = Y) (h' : X' = Y) : HEq (eqToIso h) (eqToIso h') := by
  subst X'
  rfl

private theorem evaluatedTranspose
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {L : C ⥤ D} {R : D ⥤ C} {l : c ⥤ d} {r : d ⥤ c}
    (adj : L ⊣ R) (level : l ⊣ r) (E : C ⥤ c) (F : D ⥤ d)
    (q : L ⋙ F ≅ E ⋙ l) (p : R ⋙ E ≅ F ⋙ r)
    (hu : ∀ M, E.map (adj.unit.app M) ≫ p.hom.app (L.obj M) ≫
      r.map (q.hom.app M) = level.unit.app (E.obj M))
    {M : C} {N : D} (a : L.obj M ⟶ N) :
    E.map ((adj.homEquiv M N) a) ≫ p.hom.app N =
      (level.homEquiv _ _) (q.inv.app M ≫ F.map a) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hp := p.hom.naturality a
  dsimp only [Functor.comp_map] at hp
  rw [hp]
  have hu' : E.map (adj.unit.app M) ≫ p.hom.app (L.obj M) =
      level.unit.app (E.obj M) ≫ r.map (q.inv.app M) := by
    rw [← hu M]
    simp only [Category.assoc, ← r.map_comp, Iso.hom_inv_id_app]
    erw [r.map_id, Category.comp_id]
  rw [← Category.assoc, hu', Category.assoc]

private theorem evaluatedConjugate
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} {l₁ l₂ : c ⥤ d} {r₁ r₂ : d ⥤ c}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂) (E : C ⥤ c) (F : D ⥤ d)
    (q₁ : L₁ ⋙ F ≅ E ⋙ l₁) (p₁ : R₁ ⋙ E ≅ F ⋙ r₁)
    (q₂ : L₂ ⋙ F ≅ E ⋙ l₂) (p₂ : R₂ ⋙ E ≅ F ⋙ r₂)
    (hu₁ : ∀ M, E.map (adj₁.unit.app M) ≫ p₁.hom.app (L₁.obj M) ≫
      r₁.map (q₁.hom.app M) = level₁.unit.app (E.obj M))
    (hu₂ : ∀ M, E.map (adj₂.unit.app M) ≫ p₂.hom.app (L₂.obj M) ≫
      r₂.map (q₂.hom.app M) = level₂.unit.app (E.obj M))
    (a : L₁ ≅ L₂) (b : R₂ ≅ R₁) (α : l₁ ≅ l₂) (β : r₂ ≅ r₁)
    (ha : ∀ M, adj₁.unit.app M ≫ R₁.map (a.hom.app M) =
      adj₂.unit.app M ≫ b.hom.app (L₂.obj M))
    (hα : ∀ M, level₁.unit.app M ≫ r₁.map (α.hom.app M) =
      level₂.unit.app M ≫ β.hom.app (l₂.obj M))
    (hb : ∀ N, E.map (b.hom.app N) ≫ p₁.hom.app N =
      p₂.hom.app N ≫ β.hom.app (F.obj N)) (M : C) :
    F.map (a.hom.app M) ≫ q₂.hom.app M = q₁.hom.app M ≫ α.hom.app (E.obj M) := by
  apply (cancel_epi (q₁.inv.app M)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (level₁.homEquiv _ _).injective
  rw [level₁.homEquiv_naturality_right]
  rw [← evaluatedTranspose adj₁ level₁ E F q₁ p₁ hu₁]
  rw [Adjunction.homEquiv_unit, ha, Functor.map_comp]
  simp only [Category.assoc]
  rw [level₁.homEquiv_unit]
  rw [reassoc_of% hb]
  have hn := β.hom.naturality (q₂.hom.app M)
  simp only [Functor.comp_obj] at hn
  rw [← hn]
  have hh := congrArg (fun t ↦ t ≫ β.hom.app (l₂.obj (E.obj M))) (hu₂ M)
  rw [← hα (E.obj M)] at hh
  simpa only [Category.assoc] using hh

private def squareHorizontal
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {f : c ⥤ d} {g : d ⥤ e}
    {E₀ : C ⥤ c} {E₁ : D ⥤ d} {E₂ : E ⥤ e}
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g) :
    (F ⋙ G) ⋙ E₂ ≅ E₀ ⋙ (f ⋙ g) :=
  Functor.associator F G E₂ ≪≫ Functor.isoWhiskerLeft F qG ≪≫
    (Functor.associator F E₁ g).symm ≪≫ Functor.isoWhiskerRight qF g ≪≫
      Functor.associator E₀ f g

private theorem squareHorizontal_hom_app
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {f : c ⥤ d} {g : d ⥤ e}
    {E₀ : C ⥤ c} {E₁ : D ⥤ d} {E₂ : E ⥤ e}
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g) (M : C) :
    (squareHorizontal qF qG).hom.app M = qG.hom.app (F.obj M) ≫ g.map (qF.hom.app M) := by
  simp only [squareHorizontal, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem compositeEvaluationUnit
    {C D E c d e : Type*}
    [Category C] [Category D] [Category E] [Category c] [Category d] [Category e]
    {F : C ⥤ D} {G : D ⥤ E} {RF : D ⥤ C} {RG : E ⥤ D}
    {f : c ⥤ d} {g : d ⥤ e} {rf : d ⥤ c} {rg : e ⥤ d}
    (adjF : F ⊣ RF) (adjG : G ⊣ RG) (levelF : f ⊣ rf) (levelG : g ⊣ rg)
    (E₀ : C ⥤ c) (E₁ : D ⥤ d) (E₂ : E ⥤ e)
    (qF : F ⋙ E₁ ≅ E₀ ⋙ f) (qG : G ⋙ E₂ ≅ E₁ ⋙ g)
    (pF : RF ⋙ E₀ ≅ E₁ ⋙ rf) (pG : RG ⋙ E₁ ≅ E₂ ⋙ rg)
    (huF : ∀ M, E₀.map (adjF.unit.app M) ≫ pF.hom.app (F.obj M) ≫
      rf.map (qF.hom.app M) = levelF.unit.app (E₀.obj M))
    (huG : ∀ M, E₁.map (adjG.unit.app M) ≫ pG.hom.app (G.obj M) ≫
      rg.map (qG.hom.app M) = levelG.unit.app (E₁.obj M)) (M : C) :
    E₀.map ((adjF.comp adjG).unit.app M) ≫
      (squareHorizontal pG pF).hom.app ((F ⋙ G).obj M) ≫
      (rg ⋙ rf).map ((squareHorizontal qF qG).hom.app M) =
        (levelF.comp levelG).unit.app (E₀.obj M) := by
  simp only [squareHorizontal_hom_app, Adjunction.comp_unit_app, Functor.map_comp,
    Functor.comp_map, Functor.comp_obj, Category.assoc]
  have hp := pF.hom.naturality (adjG.unit.app (F.obj M))
  dsimp only [Functor.comp_map] at hp
  rw [reassoc_of% hp]
  have hG := congrArg rf.map (huG (F.obj M))
  simp only [Functor.map_comp] at hG
  rw [reassoc_of% hG]
  have hn := levelG.unit.naturality (qF.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
  erw [← rf.map_comp, ← hn, rf.map_comp]
  have hF := congrArg (fun t ↦ t ≫ rf.map (levelG.unit.app (f.obj (E₀.obj M)))) (huF M)
  simpa only [Category.assoc] using hF

private theorem conjugateUnit
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (a : L₁ ≅ L₂) (b : R₂ ≅ R₁)
    (ha : conjugateIsoEquiv adj₂ adj₁ a = b) (M : C) :
    adj₁.unit.app M ≫ R₁.map (a.hom.app M) =
      adj₂.unit.app M ≫ b.hom.app (L₂.obj M) := by
  have hh := unit_conjugateEquiv adj₂ adj₁ a.hom M
  have he := congrArg Iso.hom ha
  change conjugateEquiv adj₂ adj₁ a.hom = b.hom at he
  rw [he] at hh
  exact hh.symm


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The given unit-normalized evaluation, with the canonical system functor named
in its type to avoid repeated conversion of the direct-image presentations.
Source: Stacks 03D8; the primitive unit characterization
(blueprint: lem-pur-ordinary-pullback-composition-evaluation). -/
def ordinaryEvaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n ≅
      coefficientSequenceEvaluation l E Y n ⋙ integralOperationsLevelPullback l E f n :=
  PrimitiveCounit.inverseEvaluation l E f n

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] ordinaryEvaluation PrimitiveCounit.inverseEvaluation
  integralComparisonSequenceComposition Scheme.coefficientModulePullbackComposition
  Scheme.coefficientProEtaleModuleAdjunction Scheme.coefficientProEtaleModulePullback
attribute [local irreducible] Padic constantSheaf presheafToSheaf
  Scheme.coefficientProEtaleDirectRingMap
attribute [local implicit_reducible] integralCoefficientSheaf
  integralOperationsLevelPullback integralComparisonSequencePullback Scheme.ProEt
  coefficientSequenceEvaluation integralComparisonSequenceDirectImage
  Scheme.coefficientProEtaleModuleDirectImage PrimitiveCounit.inverse
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj' ModuleCat.RestrictScalars.map'

private theorem ordinaryEvaluation_heq {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    HEq (PrimitiveCounit.inverseEvaluation l E f n) (ordinaryEvaluation l E f n) := by
  unfold ordinaryEvaluation
  rfl

attribute [local irreducible] PrimitiveCounit.direct PrimitiveCounit.ringMap
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

private theorem ordinaryEvaluationUnit {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (M : coefficientSequenceModules l E Y) :
    (coefficientSequenceEvaluation l E Y n).map
        ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app M) ≫
      (EvaluationCalculus.directEvaluation l E f n).hom.app
        ((integralComparisonSequencePullback l E f).obj M) ≫
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).map
            ((ordinaryEvaluation l E f n).hom.app M) =
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).unit.app
          ((coefficientSequenceEvaluation l E Y n).obj M) := by
  exact evaluationUnit_congr
    (PrimitiveCounit.direct l E f) (integralComparisonSequenceDirectImage l E f)
    (EvaluationCalculus.direct_eq l E f)
    (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
    (integralOperationsLevelPullback l E f n)
    (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))))
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).unit
    (PrimitiveCounit.inverseEvaluation l E f n) (ordinaryEvaluation l E f n)
    (eqToIso (PrimitiveCounit.directEvaluation_eq l E f n))
    (EvaluationCalculus.directEvaluation l E f n)
    (ordinaryEvaluation_heq l E f n)
    (by
      unfold EvaluationCalculus.directEvaluation
      exact eqToIso_heq (congrArg (fun R ↦ R ⋙ coefficientSequenceEvaluation l E Y n)
        (EvaluationCalculus.direct_eq l E f)) _ _)
    (EvaluationCalculus.primitiveEvaluationUnit l E f n) M

private theorem evaluation_map_apply (X : Scheme.{t}) (n : ℕ)
    {N N' : coefficientSequenceModules l E X} (a : N ⟶ N') (U : X.ProEt)
    (x : N.val.obj (op (n, U))) :
    ((coefficientSequenceEvaluation l E X n).map a).val.app (op U) x =
      a.val.app (op (n, U)) x := by
  rfl

private theorem finiteDirect_map_apply {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    {N N' : normalizedDVRModules l E X n} (a : N ⟶ N') (U : Y.ProEt)
    (x : N.val.obj (op ((Scheme.proEtaleBaseChange f).obj U))) :
    ((Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).map a).val.app (op U) x =
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj U)) x := by
  rfl

private theorem evaluatedRightSquare {X Y Z : Scheme.{t}}
    (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ)
    (d : integralComparisonSequenceDirectImage l E h ⋙
      integralComparisonSequenceDirectImage l E f ≅
        integralComparisonSequenceDirectImage l E (h ≫ f))
    (δ : (Scheme.coefficientProEtaleModuleDirectImage.{t, u} h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⋙
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≅
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))))
    (hd : ∀ (N : coefficientSequenceModules l E Z) (U : Y.ProEt)
      (x : ((integralComparisonSequenceDirectImage l E h ⋙
        integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U))),
      (d.hom.app N).val.app (op (n, U)) x =
        N.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackComp
            (P := (show MorphismProperty Scheme.{t} from @WeaklyEtale))
            (Q := ⊤) h f).hom.app U)).op x)
    (hδ : ∀ (N : normalizedDVRModules l E Z n) (U : Y.ProEt)
      (x : (((Scheme.coefficientProEtaleModuleDirectImage.{t, u} h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ⋙
      (Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).obj N).val.obj
        (op U)),
      (δ.hom.app N).val.app (op U) x =
        N.val.map ((MorphismProperty.Over.pullbackComp
          (P := (show MorphismProperty Scheme.{t} from @WeaklyEtale))
          (Q := ⊤) h f).hom.app U).op x) :
    ∀ N : coefficientSequenceModules l E Z,
      (coefficientSequenceEvaluation l E Y n).map (d.hom.app N) ≫
        (EvaluationCalculus.directEvaluation l E (h ≫ f) n).hom.app N =
      (squareHorizontal (EvaluationCalculus.directEvaluation l E h n)
        (EvaluationCalculus.directEvaluation l E f n)).hom.app N ≫
        δ.hom.app ((coefficientSequenceEvaluation l E Z n).obj N) := by
  intro N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨U⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [squareHorizontal_hom_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, CategoryTheory.comp_apply]
  change ((integralComparisonSequenceDirectImage l E h ⋙
    integralComparisonSequenceDirectImage l E f).obj N).val.obj (op (n, U)) at x
  have hl := (congrArg
    (((EvaluationCalculus.directEvaluation l E (h ≫ f) n).hom.app N).val.app (op U))
    (evaluation_map_apply l E Y n (d.hom.app N) U x)).trans
      (EvaluationCalculus.directEvaluation_apply l E (h ≫ f) n N U
        ((d.hom.app N).val.app (op (n, U)) x))
  have hr := (congrArg
    (fun z ↦ ((Scheme.coefficientProEtaleModuleDirectImage.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).map
      ((EvaluationCalculus.directEvaluation l E h n).hom.app N)).val.app (op U) z)
    (EvaluationCalculus.directEvaluation_apply l E f n
      ((integralComparisonSequenceDirectImage l E h).obj N) U x)).trans
      ((finiteDirect_map_apply l E f n
        ((EvaluationCalculus.directEvaluation l E h n).hom.app N) U x).trans
        (EvaluationCalculus.directEvaluation_apply l E h n N
          ((Scheme.proEtaleBaseChange f).obj U) x))
  exact hl.trans ((hd N U x).trans
    ((hδ ((coefficientSequenceEvaluation l E Z n).obj N) U x).symm.trans
      (congrArg ((δ.hom.app ((coefficientSequenceEvaluation l E Z n).obj N)).val.app
        (op U)) hr).symm))

/-- Ordinary evaluation respects the two adjunction-normalized compositors.
Source: Stacks Project, sites-modules.tex, Tag 03D8; parent proof steps 1 and 3.
(blueprint: lem-pur-ordinary-pullback-composition-evaluation).
Proof: transpose each composite under the finite inverse-image/direct-image
adjunctions. The defining unit equations for inverseEvaluation identify the
transposed evaluation comparisons with the identities on evaluated direct images.
The defining mate equations for the system and finite compositors identify the
remaining maps with their direct-image fibre-product pasting maps. On a section
at (n,U), both maps are restriction along the same canonical isomorphism
Z x_X (X x_Y U) -> Z x_Y U. Their coefficient actions agree since each
constant-section map sends a scalar to its constant section. The maps agree on
all sections, hence as module-sheaf maps; injectivity of the adjunction Hom
equivalences gives the displayed equality. This works for every strict system M,
with arbitrary transition maps, and for n=0 (the first positive quotient). -/
theorem ordinaryCompositionEvaluation {X Y Z : Scheme.{t}}
    (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ) (M : coefficientSequenceModules l E Y) :
    (ordinaryEvaluation l E (h ≫ f) n).inv.app M ≫
      (coefficientSequenceEvaluation l E Z n).map
        ((integralComparisonSequenceComposition l E h f).hom.app M) =
    (Scheme.coefficientModulePullbackComposition h f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
          ((coefficientSequenceEvaluation l E Y n).obj M) ≫
      (integralOperationsLevelPullback l E h n).map
        ((ordinaryEvaluation l E f n).inv.app M) ≫
      (ordinaryEvaluation l E h n).inv.app
        ((integralComparisonSequencePullback l E f).obj M) := by
  obtain ⟨d, he, hd⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h f).exists.choose_spec
  obtain ⟨δ, hδ, hα⟩ :=
    (Scheme.coefficientModulePullbackComposition_existsUnique h f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).exists.choose_spec
  have hsys : conjugateIsoEquiv
      ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).comp
        (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f)))
      (integralComparisonSequenceComposition l E h f) = d := by
    simpa only [integralComparisonSequenceComposition] using he
  have hlev : conjugateIsoEquiv
      ((Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))).comp
        (Scheme.coefficientProEtaleModuleAdjunction.{t, u} h
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1))))))
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} (h ≫ f)
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))
      (Scheme.coefficientModulePullbackComposition h f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))) = δ := by
    simpa only [Scheme.coefficientModulePullbackComposition] using hδ
  have hb := evaluatedRightSquare l E h f n d δ (fun N U x ↦ hd N n U x) hα
  have hh := evaluatedConjugate
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f)))
    ((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).comp
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)))
    (Scheme.coefficientProEtaleModuleAdjunction.{t, u} (h ≫ f)
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1)))))
    ((Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).comp
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} h
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))))
    (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E Z n)
    (ordinaryEvaluation l E (h ≫ f) n) (EvaluationCalculus.directEvaluation l E (h ≫ f) n)
    (squareHorizontal (ordinaryEvaluation l E f n) (ordinaryEvaluation l E h n))
    (squareHorizontal (EvaluationCalculus.directEvaluation l E h n)
      (EvaluationCalculus.directEvaluation l E f n))
    (ordinaryEvaluationUnit l E (h ≫ f) n)
    (compositeEvaluationUnit
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} f
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))
      (Scheme.coefficientProEtaleModuleAdjunction.{t, u} h
        (CommRingCat.of (ULift.{t + 1}
          (Padic.coefficientExtensionRing l E (n + 1)))))
      (coefficientSequenceEvaluation l E Y n) (coefficientSequenceEvaluation l E X n)
      (coefficientSequenceEvaluation l E Z n)
      (ordinaryEvaluation l E f n) (ordinaryEvaluation l E h n)
      (EvaluationCalculus.directEvaluation l E f n) (EvaluationCalculus.directEvaluation l E h n)
      (ordinaryEvaluationUnit l E f n) (ordinaryEvaluationUnit l E h n))
    (integralComparisonSequenceComposition l E h f) d
    (Scheme.coefficientModulePullbackComposition h f
      (CommRingCat.of (ULift.{t + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))) δ
    (conjugateUnit _ _ _ _ hsys) (conjugateUnit _ _ _ _ hlev) hb M
  simp only [squareHorizontal_hom_app] at hh
  exact invertSquare
    ((ordinaryEvaluation l E (h ≫ f) n).app M)
    ((ordinaryEvaluation l E h n).app ((integralComparisonSequencePullback l E f).obj M))
    ((integralOperationsLevelPullback l E h n).mapIso
      ((ordinaryEvaluation l E f n).app M)) _ _ hh

end WeilConjectures.PullbackCompositionTransport
