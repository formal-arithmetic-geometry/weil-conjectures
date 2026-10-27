/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.Paper.DerivedTowerEvaluationNormalization
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor

/-! # Exact pullback and normalized strict-tower derived comparisons

Source: the retained localization Step 6, ordinary and tower comparisons, in
`sec-smooth-purity/sk-prop-sf-localization/prop-sf-localization-all-stages.md`;
Stacks Tags 015F and 06XN (left-derived duals)
(blueprint: lem-sf-exact-pullback-tower-counit-comparison).

Level `n : ℕ` is positive level `n + 1`. All derived categories are unbounded.
The evaluation interchange is the existing canonical composition comparison
for exact descent, whose ordinary comparison is the degreewise identity.
-/

@[expose] public section

set_option autoImplicit false

universe u wA wB wTA wTB

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.DerivedTowerPullback

namespace CategoryTheory.ExactPullbackTower

private theorem derivedComposition_fac
    {A : Type*} {B : Type*} {C : Type*}
    [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app K := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G K
  have hid : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K =
      𝟙 _ := rfl
  erw [hid, DerivedCategory.Q.map_id, Category.comp_id] at h
  exact h

private theorem towerInterchange_fac
    {A : Type*} {B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (F : B ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℕᵒᵖ) (K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    (towerDerivedEvaluationInterchange F n).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategory.map
          (((evaluation ℕᵒᵖ B).obj n).mapDerivedCategoryFactors.hom.app K) ≫
        F.mapDerivedCategoryFactors.hom.app
          ((((evaluation ℕᵒᵖ B).obj n).mapHomologicalComplex (.up ℤ)).obj K) =
      ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory.map
          (((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapDerivedCategoryFactors.hom.app K) ≫
        ((evaluation ℕᵒᵖ A).obj n).mapDerivedCategoryFactors.hom.app
          ((((Functor.whiskeringRight ℕᵒᵖ B A).obj F).mapHomologicalComplex (.up ℤ)).obj K) := by
  let FT := (Functor.whiskeringRight ℕᵒᵖ B A).obj F
  let EA := (evaluation ℕᵒᵖ A).obj n
  let EB := (evaluation ℕᵒᵖ B).obj n
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso FT EA).hom.app (DerivedCategory.Q.obj K))).mp
  dsimp only [FT, EA, EB]
  simp only [towerDerivedEvaluationInterchange, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact (derivedComposition_fac EB F K).trans (derivedComposition_fac FT EA K).symm

private theorem exact_comparison
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (G F : A ⥤ B) [G.Additive] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (m : G ≅ F)
    (L : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso A (.up ℤ))] :
    ∃ e : L ≅ F.mapDerivedCategory,
      (∀ P : CochainComplex A ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
          ε.app P ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)) ∧
      (∀ e' : L ≅ F.mapDerivedCategory,
        (∀ P : CochainComplex A ℤ,
          e'.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
            ε.app P ≫ DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)) → e' = e) ∧
      ∀ P : CochainComplex A ℤ, IsIso (ε.app P) := by
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    (Functor.exactFunctor_derivedFunctor F F.mapDerivedCategory
      F.mapDerivedCategoryFactors).2.1
  let μ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex m (.up ℤ))
    (DerivedCategory.Q (C := B))
  let e := Functor.leftDerivedNatIso L F.mapDerivedCategory ε
    F.mapDerivedCategoryFactors.hom W μ
  have he (P : CochainComplex A ℤ) :
      e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        ε.app P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P) :=
    Functor.leftDerivedNatTrans_app L F.mapDerivedCategory ε
      F.mapDerivedCategoryFactors.hom W μ.hom P
  refine ⟨e, he, ?_, ?_⟩
  · intro e' he'
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q W
    intro P
    exact (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).1
      ((he' P).trans (he P).symm)
  · intro P
    have h : IsIso (ε.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)) := by
      rw [← he P]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P))

/-- Unique universal ordinary and strict-tower comparisons for an exact module pullback,
with invertible counits, counit-normalized evaluation, and every transition equation.
Source: the blueprint localization Step 6 through immersion-comparison Step 1,
old normalization Steps 1--3; Stacks Tags 015F and 06XN, left-derived duals
(blueprint: lem-sf-exact-pullback-tower-counit-comparison).

The adjunction `G ⊣ f.modules` specifies the usual inverse image followed by extension
of scalars, using the same interface as `diagram_pullback_quasiIso`. Universal pairs
are specified independently of exact descent. Their computation on objectwise K-flat
flat-term representatives follows from the ringed-site resolving class.

Proof:
1. By lem-weil-pbc-exact-functor-derived-functor, exact descent with its localization
comparison is universal. Compose the given universal counit with the image of `m`.
This preserves universality, by composing test transformations with the inverse of `m`.
Apply lem-sfb-right-kan-extension-unique-iso to obtain unique `e` with the displayed
normalization. Solve its equation for the ordinary counit to prove invertibility.
2. By lem-weil-tower-category-levelwise-abelian, kernels and cokernels are levelwise,
so the tower extension of `F` is exact. Naturality of `m` gives its tower extension.
Repeat Step 1 to obtain unique `E` and invertibility of every tower counit.
3. Exact evaluation descends by lem-weil-pbc-exact-functor-derived-factorization.
The identity commuting termwise `F` and evaluation lifts uniquely by
lem-weil-pbc-localization-universal-property to `towerDerivedEvaluationInterchange F (op n)`.
Conjugate evaluation of `E` by this interchange and the inverse of `e`.
4. On every tower complex, the two comparison equations and the interchange equation
give `Q(m) ε w = Q(m) ev(τ)`. Cancel `Q(m)` to get the actual counit normalization.
The objectwise K-flat flat-term class resolves by lem-weil-pbc-diagram-kflat-replacements.
Apply lem-cbc-derived-tower-evaluation-normalization to identify `w` with its unique
normalized evaluation comparison `v`. Its transition equations give all `b ≥ a`,
including `b = a`. These arguments apply to unbounded complexes throughout. -/
theorem exists_unique_counit_comparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (G F : Modules R ⥤ Modules S) [G.Additive] (adj : G ⊣ f.modules)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] (m : G ≅ F)
    [HasDerivedCategory.{wA} (Modules R)] [HasDerivedCategory.{wB} (Modules S)]
    [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ Modules R)]
    [HasDerivedCategory.{wTB} (ℕᵒᵖ ⥤ Modules S)]
    (L : DerivedCategory (Modules R) ⥤ DerivedCategory (Modules S))
    (Lt : DerivedCategory (ℕᵒᵖ ⥤ Modules R) ⥤ DerivedCategory (ℕᵒᵖ ⥤ Modules S))
    (ε : DerivedCategory.Q ⋙ L ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (τ : DerivedCategory.Q ⋙ Lt ⟶
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj G).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q)
    [L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Modules R) (.up ℤ))]
    [Lt.IsLeftDerivedFunctor τ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ Modules R) (.up ℤ))] :
    ∃ (e : L ≅ F.mapDerivedCategory)
      (E : Lt ≅ Functor.mapDerivedCategory
        ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F)),
      (∀ P : CochainComplex (Modules R) ℤ,
        e.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
          ε.app P ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)) ∧
      (∀ e' : L ≅ F.mapDerivedCategory,
        (∀ P : CochainComplex (Modules R) ℤ,
          e'.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
            ε.app P ≫ DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex m (.up ℤ)).hom.app P)) → e' = e) ∧
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ,
        E.hom.app (DerivedCategory.Q.obj M) ≫
            (Functor.mapDerivedCategoryFactors
              ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F)).hom.app M =
          τ.app M ≫ DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).mapIso m)
              (.up ℤ)).hom.app M)) ∧
      (∀ E' : Lt ≅ Functor.mapDerivedCategory
          ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F),
        (∀ M : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ,
          E'.hom.app (DerivedCategory.Q.obj M) ≫
              (Functor.mapDerivedCategoryFactors
                ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F)).hom.app M =
            τ.app M ≫ DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex
                ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).mapIso m)
                (.up ℤ)).hom.app M)) → E' = E) ∧
      (∀ P : CochainComplex (Modules R) ℤ, IsIso (ε.app P)) ∧
      (∀ M : CochainComplex (ℕᵒᵖ ⥤ Modules R) ℤ, IsIso (τ.app M)) ∧
      ∃ v : ∀ n : ℕ, Comparison (A := Modules R) (B := Modules S) L Lt n,
        (∀ n : ℕ, IsNormalizedOn G L Lt ε τ (IsGoodTower R) n (v n)) ∧
        (∀ (n : ℕ) (v' : Comparison (A := Modules R) (B := Modules S) L Lt n),
          IsNormalizedOn G L Lt ε τ (IsGoodTower R) n v' → v' = v n) ∧
        (∀ (n : ℕ) (N : DerivedCategory (ℕᵒᵖ ⥤ Modules R)),
          ((evaluation ℕᵒᵖ (Modules S)).obj (op n)).mapDerivedCategory.map (E.hom.app N) ≫
              (towerDerivedEvaluationInterchange F (op n)).hom.app N =
            (v n).hom.app N ≫
              e.hom.app (((evaluation ℕᵒᵖ (Modules R)).obj (op n)).mapDerivedCategory.obj N)) ∧
        ∀ (a b : ℕ) (h : a ≤ b) (N : DerivedCategory (ℕᵒᵖ ⥤ Modules R)),
          (v b).hom.app N ≫ L.map ((derivedTransition (A := Modules R) a b h).app N) =
            (derivedTransition (A := Modules S) a b h).app (Lt.obj N) ≫ (v a).hom.app N := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    obtain ⟨e, he, hue, hε⟩ := exact_comparison G F m L ε
    obtain ⟨E, hE, huE, hτ⟩ := exact_comparison
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj G)
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).obj F)
      ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).mapIso m) Lt τ
    obtain ⟨v, hv, huv, htrans⟩ :=
      exists_unique_normalized_evaluation J K R S f G adj L Lt ε τ
    refine ⟨e, E, he, hue, hE, huE, hε, hτ, v, hv, huv, ?_, htrans⟩
    have hw (n : ℕ) : ∃ w : Comparison (A := Modules R) (B := Modules S) L Lt n,
        IsNormalizedOn G L Lt ε τ (IsGoodTower R) n w ∧
        ∀ N, ((evaluation ℕᵒᵖ (Modules S)).obj (op n)).mapDerivedCategory.map
            (E.hom.app N) ≫ (towerDerivedEvaluationInterchange F (op n)).hom.app N =
          w.hom.app N ≫ e.hom.app
            (((evaluation ℕᵒᵖ (Modules R)).obj (op n)).mapDerivedCategory.obj N) := by
      let EA := (evaluation ℕᵒᵖ (Modules R)).obj (op n)
      let EB := (evaluation ℕᵒᵖ (Modules S)).obj (op n)
      let w : Comparison (A := Modules R) (B := Modules S) L Lt n :=
        Functor.isoWhiskerRight E EB.mapDerivedCategory ≪≫
          towerDerivedEvaluationInterchange F (op n) ≪≫
          Functor.isoWhiskerLeft EA.mapDerivedCategory e.symm
      have hwfac (N : DerivedCategory (ℕᵒᵖ ⥤ Modules R)) :
          EB.mapDerivedCategory.map (E.hom.app N) ≫
              (towerDerivedEvaluationInterchange F (op n)).hom.app N =
            w.hom.app N ≫ e.hom.app (EA.mapDerivedCategory.obj N) := by
        simp only [w, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
          Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
          Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app]
        exact congrArg (fun t ↦ EB.mapDerivedCategory.map (E.hom.app N) ≫ t)
          (Category.comp_id ((towerDerivedEvaluationInterchange F (op n)).hom.app N)).symm
      refine ⟨w, ?_, hwfac⟩
      intro P _
      have := hε (P.asFunctor.obj (op n))
      let μ := (NatIso.mapHomologicalComplex m (.up ℤ)).hom
      let μt := (NatIso.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules R) (Modules S)).mapIso m) (.up ℤ)).hom
      apply (cancel_mono (DerivedCategory.Q.map (μ.app (P.asFunctor.obj (op n))))).1
      simp only [Category.assoc]
      rw [← he]
      erw [e.hom.naturality_assoc]
      rw [← Category.assoc (w.hom.app _), ← hwfac]
      erw [Category.assoc, towerInterchange_fac F (op n) P,
        ← EB.mapDerivedCategory.map_comp_assoc, hE]
      rw [EB.mapDerivedCategory.map_comp, Category.assoc]
      have hn := EB.mapDerivedCategoryFactors.hom.naturality (μt.app P)
      dsimp only [Functor.comp_map] at hn
      rw [hn]
      simp only [← DerivedCategory.Q.map_comp]
      congr 2
    intro n N
    obtain ⟨w, hwn, hwfac⟩ := hw n
    rw [huv n w hwn] at hwfac
    exact hwfac N

end CategoryTheory.ExactPullbackTower
