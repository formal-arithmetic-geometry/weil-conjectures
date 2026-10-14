/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.ModuleCupCosimplicialAWNaturality
public import Sheaf.Paper.ModuleCupGodementModel
import Sheaf.Paper.ModuleCupGodementModelsExist
import Sheaf.Paper.ModuleCupGodementPairingsFromBeta
import Sheaf.Paper.ModuleCupGodementIteratePairingsCanonicalCollapse
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import all Sheaf.Paper.ModuleCupGodementRelations

/-! # Compatible Godement models for coefficient morphisms -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private def iterateMap (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    (n : ℕ) → (moduleCup_godementIterate X F n ⟶ moduleCup_godementIterate X G n)
  | 0 => f
  | n + 1 => moduleCup_godementMap X (iterateMap X f n)

private theorem iterateMap_insert (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementInsert X F n i ≫ iterateMap X f (n + 1) =
      iterateMap X f n ≫ moduleCup_godementInsert X G n i := by
  induction n with
  | zero =>
    have hi : i = 0 := by
      apply Fin.ext
      have := i.isLt
      omega
    subst i
    exact unit_natural X f
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hz (H : X.Modules) : moduleCup_godementInsert X H (n + 1) 0 =
          moduleCup_godementUnit X (moduleCup_godementIterate X H (n + 1)) := by
        simp [moduleCup_godementInsert]
      rw [hz, hz]
      exact unit_natural X (iterateMap X f (n + 1))
    · have hs (H : X.Modules) : moduleCup_godementInsert X H (n + 1) j.succ =
          moduleCup_godementMap X (moduleCup_godementInsert X H n j) := by
        simp [moduleCup_godementInsert, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X _ ≫ moduleCup_godementMap X _ =
        moduleCup_godementMap X _ ≫ moduleCup_godementMap X _
      rw [← map_comp, ← map_comp, ih]

private theorem iterateMap_collapse (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementCollapse X F n i ≫ iterateMap X f (n + 1) =
      iterateMap X f (n + 2) ≫ moduleCup_godementCollapse X G n i := by
  induction n with
  | zero =>
    have hi : i = 0 := by
      apply Fin.ext
      have := i.isLt
      omega
    subst i
    exact multiply_natural X f
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hz (H : X.Modules) : moduleCup_godementCollapse X H (n + 1) 0 =
          moduleCup_godementMultiply X (moduleCup_godementIterate X H (n + 1)) := by
        simp [moduleCup_godementCollapse]
      rw [hz, hz]
      exact multiply_natural X (iterateMap X f (n + 1))
    · have hs (H : X.Modules) : moduleCup_godementCollapse X H (n + 1) j.succ =
          moduleCup_godementMap X (moduleCup_godementCollapse X H n j) := by
        simp [moduleCup_godementCollapse, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X _ ≫ moduleCup_godementMap X _ =
        moduleCup_godementMap X _ ≫ moduleCup_godementMap X _
      rw [← map_comp, ← map_comp, ih]

private theorem modelMap (X : Scheme.{u}) {F G : X.Modules} (q : F ⟶ G)
    (A B : CosimplicialObject X.Modules)
    (eA : ∀ n : ℕ, A.obj ⦋n⦌ = moduleCup_godementIterate X F (n + 1))
    (eB : ∀ n : ℕ, B.obj ⦋n⦌ = moduleCup_godementIterate X G (n + 1))
    (hAδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (eA n) ≫ moduleCup_godementInsert X F (n + 1) i =
        A.map (SimplexCategory.δ i) ≫ eqToHom (eA (n + 1)))
    (hBδ : ∀ (n : ℕ) (i : Fin (n + 2)),
      eqToHom (eB n) ≫ moduleCup_godementInsert X G (n + 1) i =
        B.map (SimplexCategory.δ i) ≫ eqToHom (eB (n + 1)))
    (hAσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      eqToHom (eA (n + 1)) ≫ moduleCup_godementCollapse X F n i =
        A.map (SimplexCategory.σ i) ≫ eqToHom (eA n))
    (hBσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      eqToHom (eB (n + 1)) ≫ moduleCup_godementCollapse X G n i =
        B.map (SimplexCategory.σ i) ≫ eqToHom (eB n)) :
    ∃ f : A ⟶ B, ∀ n : SimplexCategory,
      f.app n = eqToHom (eA n.len) ≫ iterateMap X q (n.len + 1) ≫
        eqToHom (eB n.len).symm := by
  let app : ∀ n : SimplexCategory, A.obj n ⟶ B.obj n :=
    fun n ↦ eqToHom (eA n.len) ≫ iterateMap X q (n.len + 1) ≫
      eqToHom (eB n.len).symm
  have hδ (n : ℕ) (i : Fin (n + 2)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.δ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono (eqToHom (eB (n + 1)))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hBδ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [← hAδ n i]
    simp only [Category.assoc]
    rw [iterateMap_insert]
  have hσ (n : ℕ) (i : Fin (n + 1)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.σ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono (eqToHom (eB n))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hBσ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [← hAσ n i]
    simp only [Category.assoc]
    rw [iterateMap_collapse]
  have hnat := SimplexCategory.morphismProperty_eq_top
    (MorphismProperty.naturalityProperty app) (fun {_} ↦ hδ _) (fun {_} ↦ hσ _)
  exact ⟨{ app := app
           naturality := fun _ _ f ↦ by
             have h : (MorphismProperty.naturalityProperty app) f := by rw [hnat]; trivial
             exact h }, fun _ ↦ rfl⟩

private theorem pairingForModels (X : Scheme.{u}) (F G : X.Modules)
    (A B C : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
      (((alternatingCofaceMapComplex X.Modules).obj B).extend
        ComplexShape.embeddingUpNat))
    (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
      (((alternatingCofaceMapComplex X.Modules).obj C).extend
        ComplexShape.embeddingUpNat))
    (hA : ModuleCupGodementModel X F A a)
    (hB : ModuleCupGodementModel X G B b)
    (hC : ModuleCupGodementModel X (F ⊗ G) C c)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies X G B)
    (sC : ModuleCupGodementCodegeneracies X (F ⊗ G) C)
    (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
      moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n)
    (hp0 : p 0 = 𝟙 (F ⊗ G))
    (hpδ : ∀ (n : ℕ) (i : Fin (n + 1)),
      (moduleCup_godementInsert X F n i ⊗ₘ moduleCup_godementInsert X G n i) ≫
        p (n + 1) = p n ≫ moduleCup_godementInsert X (F ⊗ G) n i)
    (hpσ : ∀ (n : ℕ) (i : Fin (n + 1)),
      (moduleCup_godementCollapse X F n i ⊗ₘ moduleCup_godementCollapse X G n i) ≫
        p (n + 1) = p (n + 2) ≫ moduleCup_godementCollapse X (F ⊗ G) n i) :
    ∃ μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj
        (C := SimplexCategory) (D := X.Modules) A B ⟶ C,
      (∀ n : SimplexCategory, μ.app n =
        (eqToHom (hA.choose n.len) ⊗ₘ eqToHom (hB.choose n.len)) ≫
          p (n.len + 1) ≫ eqToHom (hC.choose n.len).symm) ∧
      ((a.f 0) ⊗ₘ (b.f 0)) ≫
        ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom ⊗ₘ
          (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫ μ.app ⦋0⦌ ≫
          (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).inv = c.f 0 := by
  obtain ⟨eA, hAδ, hAa⟩ := hA
  obtain ⟨eB, hBδ, hBb⟩ := hB
  obtain ⟨eC, hCδ, hCc⟩ := hC
  obtain ⟨eA', hAσ⟩ := sA
  obtain ⟨eB', hBσ⟩ := sB
  obtain ⟨eC', hCσ⟩ := sC
  have hσA := (show eA' = eA from Subsingleton.elim _ _) ▸ hAσ
  have hσB := (show eB' = eB from Subsingleton.elim _ _) ▸ hBσ
  have hσC := (show eC' = eC from Subsingleton.elim _ _) ▸ hCσ
  let app : ∀ d : SimplexCategory,
      (CategoryTheory.Monoidal.FunctorCategory.tensorObj A B).obj d ⟶ C.obj d :=
    fun d ↦ (eqToHom (eA d.len) ⊗ₘ eqToHom (eB d.len)) ≫
      p (d.len + 1) ≫ eqToHom (eC d.len).symm
  have hδ (n : ℕ) (i : Fin (n + 2)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.δ i) := by
    dsimp [MorphismProperty.naturalityProperty, app,
      CategoryTheory.Monoidal.FunctorCategory.tensorObj]
    apply (cancel_mono (eqToHom (eC (n + 1)))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hCδ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [tensorHom_comp_tensorHom, ← hAδ n i, ← hBδ n i]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hpδ (n + 1) i]
    simp only [Category.assoc]
  have hσ (n : ℕ) (i : Fin (n + 1)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.σ i) := by
    dsimp [MorphismProperty.naturalityProperty, app,
      CategoryTheory.Monoidal.FunctorCategory.tensorObj]
    apply (cancel_mono (eqToHom (eC n))).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [← hσC n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [tensorHom_comp_tensorHom, ← hσA n i, ← hσB n i]
    rw [← tensorHom_comp_tensorHom, Category.assoc, hpσ n i]
    simp only [Category.assoc]
  have hnat := SimplexCategory.morphismProperty_eq_top
    (MorphismProperty.naturalityProperty app) (fun {_} ↦ hδ _) (fun {_} ↦ hσ _)
  let μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj A B ⟶ C :=
    { app := app
      naturality := fun d e f ↦ by
        have h : (MorphismProperty.naturalityProperty app) f := by rw [hnat]; trivial
        exact h }
  refine ⟨μ, fun _ ↦ rfl, ?_⟩
  dsimp [μ, app]
  apply (cancel_mono
    ((((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
      ComplexShape.embeddingUpNat (i := 0) rfl).hom ≫ eqToHom (eC 0))).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [hAa, hBb, hCc]
  rw [← tensorHom_comp_tensorHom_assoc]
  have hu := hpδ 0 (0 : Fin 1)
  simp only [moduleCup_godementInsert, hp0] at hu
  rw [hu]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom]
  change (𝟙 F ⊗ₘ 𝟙 G) ≫ 𝟙 (F ⊗ G) ≫ moduleCup_godementUnit X (F ⊗ G) =
    𝟙 (F ⊗ G) ≫ moduleCup_godementUnit X (F ⊗ G)
  simp


private theorem modelMap_augmentation (X : Scheme.{u}) {F G : X.Modules} (q : F ⟶ G)
    (A B : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A)
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
      moduleCup_cosimplicialComplex X B)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel X G B b)
    (f : A ⟶ B)
    (hf : ∀ n : SimplexCategory,
      f.app n = eqToHom (hA.choose n.len) ≫ iterateMap X q (n.len + 1) ≫
        eqToHom (hB.choose n.len).symm) :
    a ≫ moduleCup_cosimplicialMap X f =
      (CochainComplex.singleFunctor X.Modules 0).map q ≫ b := by
  apply HomologicalComplex.from_single_hom_ext
  change a.f 0 ≫ (moduleCup_cosimplicialMap X f).f 0 = q ≫ b.f 0
  apply (cancel_mono
    ((moduleCup_cosimplicialZeroIso X B).hom ≫ eqToHom (hB.choose 0))).1
  dsimp only [moduleCup_cosimplicialMap, moduleCup_cosimplicialZeroIso]
  erw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  change (a.f 0 ≫ _ ≫ f.app ⦋0⦌ ≫ _) ≫ _ = _
  rw [hf]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  have ha := hA.choose_spec.2
  have hb := hB.choose_spec.2
  calc
    _ = ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).hom ≫
        moduleCup_godementUnit X F) ≫ iterateMap X q 1 := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ iterateMap X q 1) ha
    _ = q ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 G).hom ≫
        moduleCup_godementUnit X G := by
      change (𝟙 F ≫ moduleCup_godementUnit X F) ≫ moduleCup_godementMap X q =
        q ≫ 𝟙 G ≫ moduleCup_godementUnit X G
      simpa using unit_natural X q
    _ = _ := by simpa only [Category.assoc] using congrArg (fun z ↦ q ≫ z) hb.symm

private theorem iteratePairing_natural (X : Scheme.{u})
    (β : ModuleCupGodementBeta X) (F G F₁ G₁ : X.Modules)
    (φ : F ⟶ F₁) (ψ : G ⟶ G₁)
    (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
      moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n)
    (p₁ : ∀ n : ℕ, moduleCup_godementIterate X F₁ n ⊗
      moduleCup_godementIterate X G₁ n ⟶ moduleCup_godementIterate X (F₁ ⊗ G₁) n)
    (hp0 : p 0 = 𝟙 (F ⊗ G)) (hp₁0 : p₁ 0 = 𝟙 (F₁ ⊗ G₁))
    (hprec : ∀ n, p (n + 1) = β.map _ _ ≫ moduleCup_godementMap X (p n))
    (hp₁rec : ∀ n, p₁ (n + 1) = β.map _ _ ≫ moduleCup_godementMap X (p₁ n))
    (n : ℕ) :
    p n ≫ iterateMap X (φ ⊗ₘ ψ) n =
      (iterateMap X φ n ⊗ₘ iterateMap X ψ n) ≫ p₁ n := by
  induction n with
  | zero =>
    rw [hp0, hp₁0]
    change (𝟙 (F ⊗ G) ≫ (φ ⊗ₘ ψ)) = (φ ⊗ₘ ψ) ≫ 𝟙 (F₁ ⊗ G₁)
    simp
  | succ n ih =>
    rw [hprec, hp₁rec]
    change (β.map _ _ ≫ moduleCup_godementMap X (p n)) ≫
      moduleCup_godementMap X (iterateMap X (φ ⊗ₘ ψ) n) =
      (moduleCup_godementMap X (iterateMap X φ n) ⊗ₘ
        moduleCup_godementMap X (iterateMap X ψ n)) ≫
        β.map _ _ ≫ moduleCup_godementMap X (p₁ n)
    rw [← Category.assoc _ (β.map _ _), β.naturality]
    simp only [Category.assoc]
    rw [← map_comp, ih, map_comp]

/-- Compatible augmented cosimplicial Godement models, before exactness or totalization.
Source: Stacks Project, Tag 0FKR, construction of Lemma 20.30.1 (0FKS);
Banerjee, Tensor Structure on Smooth Motives, §1.1.4, pp. 15--16.
(blueprint: lem-sc-module-cup-godement-coefficient-models)
Proof: write T for the product of the skyscrapers of the stalks. For each coefficient
sheaf H, take the cosimplicial object with degree n term T^(n+1)(H), unit-insertion
cofaces and multiplication-insertion codegeneracies. The germ maps give the augmentations.
For a morphism q, iterate the actual functorial map T(q). Naturality of the unit and
multiplication makes these iterated maps commute with the generating cofaces and
codegeneracies, hence all simplex maps. Naturality of the germ unit gives the three
augmentation squares, including q = phi tensor psi. Use the same coordinatewise
Godement tensor transformation beta for both triples. Its coefficient naturality follows
by projection to each point: both composites tensor the two induced stalk maps.
Starting with identity in degree zero of the iterates, recursively apply beta and T
to obtain the pairings. Induction using beta naturality gives their coefficient square
in every degree. The unit and multiplication identities for beta give cosimplicial
naturality; its unit identity gives the two degree-zero augmentation formulas.
Transport by the term and extension identifications to the displayed complexes. This
construction asserts no quasi-isomorphism, flasqueness, or tensor total-complex map.
For an empty scheme all coordinate checks are vacuous; zero sheaves and zero morphisms
satisfy the same formulas. -/
theorem moduleCup_godement_coefficient_models (X : Scheme.{u})
    (F G F₁ G₁ : X.Modules) (φ : F ⟶ F₁) (ψ : G ⟶ G₁) :
    ∃ (A B C A₁ B₁ C₁ : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        moduleCup_cosimplicialComplex X A)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        moduleCup_cosimplicialComplex X B)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        moduleCup_cosimplicialComplex X C)
      (a₁ : (CochainComplex.singleFunctor X.Modules 0).obj F₁ ⟶
        moduleCup_cosimplicialComplex X A₁)
      (b₁ : (CochainComplex.singleFunctor X.Modules 0).obj G₁ ⟶
        moduleCup_cosimplicialComplex X B₁)
      (c₁ : (CochainComplex.singleFunctor X.Modules 0).obj (F₁ ⊗ G₁) ⟶
        moduleCup_cosimplicialComplex X C₁)
      (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
      (μ₁ : moduleCup_cosimplicialTensor X A₁ B₁ ⟶ C₁)
      (f : A ⟶ A₁) (g : B ⟶ B₁) (k : C ⟶ C₁),
      ModuleCupGodementModel X F A a ∧ ModuleCupGodementModel X G B b ∧
      ModuleCupGodementModel X (F ⊗ G) C c ∧
      ModuleCupGodementModel X F₁ A₁ a₁ ∧ ModuleCupGodementModel X G₁ B₁ b₁ ∧
      ModuleCupGodementModel X (F₁ ⊗ G₁) C₁ c₁ ∧
      (∀ (V : X.Opens)
        (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
        (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
        (moduleCup_cosimplicialZeroPair X A B C μ).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y)) =
        (c.f 0).val.app (op V) (tmulSection x y)) ∧
      (∀ (V : X.Opens)
        (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F₁).X 0, V))
        (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G₁).X 0, V)),
        (moduleCup_cosimplicialZeroPair X A₁ B₁ C₁ μ₁).val.app (op V)
          (tmulSection ((a₁.f 0).val.app (op V) x) ((b₁.f 0).val.app (op V) y)) =
        (c₁.f 0).val.app (op V) (tmulSection x y)) ∧
      a ≫ moduleCup_cosimplicialMap X f =
        (CochainComplex.singleFunctor X.Modules 0).map φ ≫ a₁ ∧
      b ≫ moduleCup_cosimplicialMap X g =
        (CochainComplex.singleFunctor X.Modules 0).map ψ ≫ b₁ ∧
      c ≫ moduleCup_cosimplicialMap X k =
        (CochainComplex.singleFunctor X.Modules 0).map (φ ⊗ₘ ψ) ≫ c₁ ∧
      ∀ n : SimplexCategory,
        μ.app n ≫ k.app n = (f.app n ⊗ₘ g.app n) ≫ μ₁.app n := by
  obtain ⟨A, a, hA, sA⟩ := moduleCup_godement_models_exist X F
  have hAσ := (show sA.choose = hA.choose from Subsingleton.elim _ _) ▸
    sA.choose_spec
  obtain ⟨B, b, hB, sB⟩ := moduleCup_godement_models_exist X G
  have hBσ := (show sB.choose = hB.choose from Subsingleton.elim _ _) ▸
    sB.choose_spec
  obtain ⟨C, c, hC, sC⟩ := moduleCup_godement_models_exist X (F ⊗ G)
  have hCσ := (show sC.choose = hC.choose from Subsingleton.elim _ _) ▸
    sC.choose_spec
  obtain ⟨A₁, a₁, hA₁, sA₁⟩ := moduleCup_godement_models_exist X F₁
  have hA₁σ := (show sA₁.choose = hA₁.choose from Subsingleton.elim _ _) ▸
    sA₁.choose_spec
  obtain ⟨B₁, b₁, hB₁, sB₁⟩ := moduleCup_godement_models_exist X G₁
  have hB₁σ := (show sB₁.choose = hB₁.choose from Subsingleton.elim _ _) ▸
    sB₁.choose_spec
  obtain ⟨C₁, c₁, hC₁, sC₁⟩ := moduleCup_godement_models_exist X (F₁ ⊗ G₁)
  have hC₁σ := (show sC₁.choose = hC₁.choose from Subsingleton.elim _ _) ▸
    sC₁.choose_spec
  obtain ⟨β, p, hp0, hprec, hpδ⟩ :=
    moduleCup_godement_iterate_pairings_canonical_exists X F G
  obtain ⟨p₁, hp₁0, hp₁rec, hp₁δ⟩ :=
    moduleCup_godement_iterate_pairings_from_beta X F₁ G₁ β.map β.naturality β.unit
  have hpσ := moduleCup_godement_iterate_pairings_collapse_of_canonical X F G β p hp0 hprec
  have hp₁σ := moduleCup_godement_iterate_pairings_collapse_of_canonical
    X F₁ G₁ β p₁ hp₁0 hp₁rec
  obtain ⟨μ, hμapp, hμaug⟩ :=
    pairingForModels X F G A B C a b c hA hB hC sA sB sC p hp0 hpδ hpσ
  obtain ⟨μ₁, hμ₁app, hμ₁aug⟩ :=
    pairingForModels X F₁ G₁ A₁ B₁ C₁ a₁ b₁ c₁ hA₁ hB₁ hC₁ sA₁ sB₁ sC₁
      p₁ hp₁0 hp₁δ hp₁σ
  obtain ⟨f, hf⟩ := modelMap X φ A A₁ hA.choose hA₁.choose
    hA.choose_spec.1 hA₁.choose_spec.1 hAσ hA₁σ
  obtain ⟨g, hg⟩ := modelMap X ψ B B₁ hB.choose hB₁.choose
    hB.choose_spec.1 hB₁.choose_spec.1 hBσ hB₁σ
  obtain ⟨k, hk⟩ := modelMap X (φ ⊗ₘ ψ) C C₁ hC.choose hC₁.choose
    hC.choose_spec.1 hC₁.choose_spec.1 hCσ hC₁σ
  refine ⟨A, B, C, A₁, B₁, C₁, a, b, c, a₁, b₁, c₁, μ, μ₁, f, g, k,
    hA, hB, hC, hA₁, hB₁, hC₁, ?_, ?_,
    modelMap_augmentation X φ A A₁ a a₁ hA hA₁ f hf,
    modelMap_augmentation X ψ B B₁ b b₁ hB hB₁ g hg,
    modelMap_augmentation X (φ ⊗ₘ ψ) C C₁ c c₁ hC hC₁ k hk, ?_⟩
  · intro V x y
    have h := congrArg (fun q ↦ q.app V (tmulSection x y)) hμaug
    rw [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection] at h
    exact h
  · intro V x y
    have h := congrArg (fun q ↦ q.app V (tmulSection x y)) hμ₁aug
    rw [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection] at h
    exact h
  · intro n
    rw [hμapp, hk, hf, hg, hμ₁app]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.comp_id, Category.id_comp, tensorHom_comp_tensorHom_assoc]
    erw [← Category.assoc (p _) (iterateMap X (φ ⊗ₘ ψ) _),
      iteratePairing_natural X β F G F₁ G₁ φ ψ p p₁ hp0 hp₁0 hprec hp₁rec]
    simp only [tensorHom_comp_tensorHom_assoc, Category.assoc]

end
end AlgebraicGeometry.Scheme.Modules
