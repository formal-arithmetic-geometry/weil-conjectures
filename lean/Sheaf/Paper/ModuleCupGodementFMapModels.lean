/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q3 and M4
-/
module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies
public import Sheaf.Paper.ModuleCupGodementCosimplicialInput
import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Sheaf.Paper.ModuleCupGodementPairingsFromBeta
import Sheaf.Paper.ModuleCupGodementIteratePairingsCanonicalCollapse
import all Sheaf.Paper.ModuleCupGodementBetaExists

/-! # Augmented cosimplicial Godement maps across a scheme morphism

The remaining construction takes place entirely before alternating cofaces and extension by zero.
Source: Stacks Project, Tags 0FKR and 0FKU, extended by the coordinate argument below.
(blueprint: new-module-cup-godement-fmap-models).
-/

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

-- Transport a specified iterate pairing, retaining its degreewise formula.
-- This is the assembly argument of ModuleCupGodementCoefficientModels, localized
-- here so the cross-scheme construction does not import coefficient models.
private theorem pairingForModels (X : Scheme.{v}) (F G : X.Modules)
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


-- Cross-scheme maps are constructed from actual stalk and product maps.
-- All helpers in this namespace are proved; none introduces an existence assumption.
namespace FMap

private def stalk {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) (x : Y) :
    F.presheaf.stalk (f x) ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor Ab.{v} (f x)).map q.mapPresheaf ≫
    G.presheaf.stalkPushforward Ab.{v} f.base x

private theorem stalk_germ {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U) (s : Γ(F, U)) :
    stalk f q x (F.presheaf.germ U (f x) hx s) =
      G.presheaf.germ (f ⁻¹ᵁ U) x hx (q.app U s) := by
  dsimp only [stalk]
  rw [ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  change G.presheaf.stalkPushforward Ab.{v} f.base x
    (((TopCat.Presheaf.pushforward Ab.{v} f.base).obj G.presheaf).germ U (f x) hx
      (q.app U s)) = _
  erw [TopCat.Presheaf.stalkPushforward_germ_apply]

private def proj (X : Scheme.{v}) (F : X.Modules) (x : X) :
    moduleCup_godementObject X F ⟶ skyscraper x (F.presheaf.stalk x) :=
  Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x

private def coord {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) (x : Y) :
    skyscraper (f x) (F.presheaf.stalk (f x)) ⟶
      (pushforward f).obj (skyscraper x (G.presheaf.stalk x)) := by
  algebraize [(f.stalkMap x).hom]
  letI : Module (X.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
    Module.compHom (G.presheaf.stalk x) (f.stalkMap x).hom
  letI : IsScalarTower (X.presheaf.stalk (f x)) (Y.presheaf.stalk x)
      (G.presheaf.stalk x) :=
    ⟨fun r s m ↦ smul_assoc ((f.stalkMap x).hom r) s m⟩
  let l : F.presheaf.stalk (f x) →ₗ[X.presheaf.stalk (f x)] G.presheaf.stalk x :=
    stalkLinearMapMk (stalk f q x).hom fun U hx r s ↦ by
      rw [stalk_germ, stalk_germ]
      rw [Hom.app_smul]
      change G.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U r • (show Γ(G, f ⁻¹ᵁ U) from q.app U s)) = _
      rw [germ_smul]
      rw [germ_smul_eq_germ_app_smul f x (G.presheaf.stalk x) rfl hx r]
  exact toSkyscraper (l ∘ₗ skyscraperStalkEval (f x) (F.presheaf.stalk (f x))) ≫
    (pushforwardSkyscraperIso f x (G.presheaf.stalk x) rfl).inv

private theorem coord_apply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U)
    (s : Γ(skyscraper (f x) (F.presheaf.stalk (f x)), U)) :
    (coord f q x).app U s ⟨hx⟩ = stalk f q x (s ⟨hx⟩) := by
  change stalk f q x (skyscraperStalkEval (f x) (F.presheaf.stalk (f x))
    ((skyscraper (f x) (F.presheaf.stalk (f x))).presheaf.germ U (f x) hx s)) = _
  rw [skyscraperStalkEval_germ]


private def lift {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementObject X F ⟶ (pushforward f).obj (moduleCup_godementObject Y G) :=
  Pi.lift (fun x : Y ↦ proj X F (f x) ≫ coord f q x) ≫
    inv (piComparison (pushforward f) (fun x : Y ↦ skyscraper x (G.presheaf.stalk x)))

private theorem lift_proj {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) (x : Y) :
    lift f q ≫ (pushforward f).map (proj Y G x) =
      proj X F (f x) ≫ coord f q x := by
  simp only [lift, proj, Category.assoc, inv_piComparison_comp_map_π, Pi.lift_π]

private theorem lift_apply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (U : X.Opens) (hx : f x ∈ U) (s : Γ(moduleCup_godementObject X F, U)) :
    (proj Y G x).app (f ⁻¹ᵁ U) ((lift f q).app U s) ⟨hx⟩ =
      stalk f q x ((proj X F (f x)).app U s ⟨hx⟩) := by
  change ((lift f q ≫ (pushforward f).map (proj Y G x)).app U s) ⟨hx⟩ = _
  rw [lift_proj, Hom.comp_app, ConcreteCategory.comp_apply, coord_apply]

private theorem target_ext {X Y : Scheme.{v}} (f : Y ⟶ X) (G : Y.Modules)
    {P : X.Modules} (r s : P ⟶ (pushforward f).obj (moduleCup_godementObject Y G))
    (h : ∀ x : Y, r ≫ (pushforward f).map (proj Y G x) =
      s ≫ (pushforward f).map (proj Y G x)) : r = s := by
  apply (cancel_mono (piComparison (pushforward f)
    (fun x : Y ↦ skyscraper x (G.presheaf.stalk x)))).1
  apply Pi.hom_ext
  intro x
  simpa only [Category.assoc, piComparison_comp_π, proj] using h x

private theorem unit_apply (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)) :
    (proj X F x).app U ((moduleCup_godementUnit X F).app U s) ⟨hx⟩ =
      F.presheaf.germ U x hx s := by
  change ((moduleCup_godementUnit X F ≫ proj X F x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementUnit, proj, Pi.lift_π]
  erw [toSkyscraper_app_apply]
  rfl

private theorem lift_unit {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementUnit X F ≫ lift f q =
      q ≫ (pushforward f).map (moduleCup_godementUnit Y G) := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U)
    ((lift f q).app U ((moduleCup_godementUnit X F).app U s)) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementUnit Y G).app (f ⁻¹ᵁ U) (q.app U s)) ⟨hx⟩
  rw [lift_apply, unit_apply, unit_apply, stalk_germ]

private theorem stalk_precomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F H : X.Modules} {G : Y.Modules} (a : F ⟶ H)
    (q : H ⟶ (pushforward f).obj G) (x : Y) (s : F.presheaf.stalk (f x)) :
    stalk f (a ≫ q) x s = stalk f q x (a.stalkLinearMap (f x) s) := by
  obtain ⟨U, hx, s, rfl⟩ := F.presheaf.exists_germ_eq s
  rw [stalk_germ, Hom.stalkLinearMap_germ, stalk_germ]
  rfl

private theorem stalk_postcomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G H : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (b : G ⟶ H) (x : Y) (s : F.presheaf.stalk (f x)) :
    stalk f (q ≫ (pushforward f).map b) x s =
      b.stalkLinearMap x (stalk f q x s) := by
  obtain ⟨U, hx, s, rfl⟩ := F.presheaf.exists_germ_eq s
  rw [stalk_germ, stalk_germ, Hom.stalkLinearMap_germ]
  rfl

private theorem map_apply (X : Scheme.{v}) {F G : X.Modules} (q : F ⟶ G)
    (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X F, U)) :
    (proj X G x).app U ((moduleCup_godementMap X q).app U s) ⟨hx⟩ =
      q.stalkLinearMap x ((proj X F x).app U s ⟨hx⟩) := by
  change ((moduleCup_godementMap X q ≫ proj X G x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementMap, proj, Pi.lift_π, Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [toSkyscraper_app_apply]
  rw [LinearMap.comp_apply, skyscraperStalkEval_germ]

private theorem lift_precomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F H : X.Modules} {G : Y.Modules} (a : F ⟶ H)
    (q : H ⟶ (pushforward f).obj G) :
    lift f (a ≫ q) = moduleCup_godementMap X a ≫ lift f q := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U) ((lift f (a ≫ q)).app U s) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((lift f q).app U ((moduleCup_godementMap X a).app U s)) ⟨hx⟩
  rw [lift_apply, lift_apply, map_apply, stalk_precomp]

private theorem lift_postcomp {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G H : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (b : G ⟶ H) :
    lift f (q ≫ (pushforward f).map b) =
      lift f q ≫ (pushforward f).map (moduleCup_godementMap Y b) := by
  apply target_ext f H
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y H x).app (f ⁻¹ᵁ U)
      ((lift f (q ≫ (pushforward f).map b)).app U s) ⟨hx⟩ =
    (proj Y H x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementMap Y b).app (f ⁻¹ᵁ U) ((lift f q).app U s)) ⟨hx⟩
  rw [lift_apply, map_apply, lift_apply, stalk_postcomp]

private def eval (X : Scheme.{v}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem eval_germ (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(moduleCup_godementObject X F, U)) :
    eval X F x ((moduleCup_godementObject X F).presheaf.germ U x hx s) =
      (proj X F x).app U s ⟨hx⟩ := by
  rw [eval, LinearMap.comp_apply, Hom.stalkLinearMap_germ, skyscraperStalkEval_germ]

private theorem multiply_apply (X : Scheme.{v}) (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X (moduleCup_godementObject X F), U)) :
    (proj X F x).app U ((moduleCup_godementMultiply X F).app U s) ⟨hx⟩ =
      eval X F x ((proj X (moduleCup_godementObject X F) x).app U s ⟨hx⟩) := by
  change ((moduleCup_godementMultiply X F ≫ proj X F x).app U s) ⟨hx⟩ = _
  simp only [moduleCup_godementMultiply, proj, Pi.lift_π, Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [toSkyscraper_app_apply]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  erw [skyscraperStalkEval_germ]
  rfl

private theorem eval_stalk_lift {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (x : Y) (s : (moduleCup_godementObject X F).presheaf.stalk (f x)) :
    eval Y G x (stalk f (lift f q) x s) = stalk f q x (eval X F (f x) s) := by
  obtain ⟨U, hx, s, rfl⟩ := (moduleCup_godementObject X F).presheaf.exists_germ_eq s
  rw [stalk_germ, eval_germ, eval_germ, lift_apply]

private theorem lift_multiply {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G) :
    moduleCup_godementMultiply X F ≫ lift f q =
      lift f (lift f q) ≫ (pushforward f).map (moduleCup_godementMultiply Y G) := by
  apply target_ext f G
  intro x
  apply hom_ext
  intro U
  ext s
  apply SkyscraperSections.ext
  intro hx
  change (proj Y G x).app (f ⁻¹ᵁ U)
    ((lift f q).app U ((moduleCup_godementMultiply X F).app U s)) ⟨hx⟩ =
    (proj Y G x).app (f ⁻¹ᵁ U)
      ((moduleCup_godementMultiply Y G).app (f ⁻¹ᵁ U)
        ((lift f (lift f q)).app U s)) ⟨hx⟩
  rw [lift_apply, multiply_apply, multiply_apply, lift_apply, eval_stalk_lift]

private def iterate {X Y : Scheme.{v}} (f : Y ⟶ X) {F : X.Modules} {G : Y.Modules}
    (q : F ⟶ (pushforward f).obj G) : (n : ℕ) →
      (moduleCup_godementIterate X F n ⟶
        (pushforward f).obj (moduleCup_godementIterate Y G n))
  | 0 => q
  | n + 1 => lift f (iterate f q n)

private theorem iterate_insert {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementInsert X F n i ≫ iterate f q (n + 1) =
      iterate f q n ≫ (pushforward f).map (moduleCup_godementInsert Y G n i) := by
  induction n with
  | zero => exact lift_unit f q
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [moduleCup_godementInsert, Fin.val_zero, ↓reduceDIte]
      exact lift_unit f (iterate f q (n + 1))
    · have hs (Z : Scheme.{v}) (H : Z.Modules) :
          moduleCup_godementInsert Z H (n + 1) j.succ =
            moduleCup_godementMap Z (moduleCup_godementInsert Z H n j) := by
        simp [moduleCup_godementInsert, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X (moduleCup_godementInsert X F n j) ≫
          lift f (iterate f q (n + 1)) =
        lift f (iterate f q n) ≫
          (pushforward f).map (moduleCup_godementMap Y (moduleCup_godementInsert Y G n j))
      rw [← lift_precomp, ih, lift_postcomp]

private theorem iterate_collapse {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (n : ℕ) (i : Fin (n + 1)) :
    moduleCup_godementCollapse X F n i ≫ iterate f q (n + 1) =
      iterate f q (n + 2) ≫ (pushforward f).map (moduleCup_godementCollapse Y G n i) := by
  induction n with
  | zero => exact lift_multiply f q
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [moduleCup_godementCollapse, Fin.val_zero, ↓reduceDIte]
      exact lift_multiply f (iterate f q (n + 1))
    · have hs (Z : Scheme.{v}) (H : Z.Modules) :
          moduleCup_godementCollapse Z H (n + 1) j.succ =
            moduleCup_godementMap Z (moduleCup_godementCollapse Z H n j) := by
        simp [moduleCup_godementCollapse, Fin.val_succ]
      rw [hs, hs]
      change moduleCup_godementMap X (moduleCup_godementCollapse X F n j) ≫
          lift f (iterate f q (n + 1)) =
        lift f (iterate f q (n + 2)) ≫
          (pushforward f).map (moduleCup_godementMap Y (moduleCup_godementCollapse Y G n j))
      rw [← lift_precomp, ih, lift_postcomp]

private theorem modelMap {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (A : CosimplicialObject X.Modules) (B : CosimplicialObject Y.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A)
    (b : (CochainComplex.singleFunctor Y.Modules 0).obj G ⟶
      moduleCup_cosimplicialComplex Y B)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel Y G B b)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies Y G B) :
    ∃ g : A ⟶ B ⋙ pushforward f, ∀ n : SimplexCategory,
      g.app n = eqToHom (hA.choose n.len) ≫ iterate f q (n.len + 1) ≫
        (pushforward f).map (eqToHom (hB.choose n.len).symm) := by
  let eA := hA.choose
  let eB := hB.choose
  have hAδ := hA.choose_spec.1
  have hBδ := hB.choose_spec.1
  have hAσ := (show sA.choose = eA from Subsingleton.elim _ _) ▸ sA.choose_spec
  have hBσ := (show sB.choose = eB from Subsingleton.elim _ _) ▸ sB.choose_spec
  let app : ∀ n : SimplexCategory, A.obj n ⟶ (B ⋙ pushforward f).obj n :=
    fun n ↦ eqToHom (eA n.len) ≫ iterate f q (n.len + 1) ≫
      (pushforward f).map (eqToHom (eB n.len).symm)
  have hδ (n : ℕ) (i : Fin (n + 2)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.δ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono ((pushforward f).map (eqToHom (eB (n + 1))))).1
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    erw [← hBδ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    erw [← hAδ n i]
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z ↦ eqToHom (eA n) ≫ z)
      (iterate_insert f q (n + 1) i)
  have hσ (n : ℕ) (i : Fin (n + 1)) :
      (MorphismProperty.naturalityProperty app) (SimplexCategory.σ i) := by
    dsimp [MorphismProperty.naturalityProperty, app]
    apply (cancel_mono ((pushforward f).map (eqToHom (eB n)))).1
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    simp only [Category.comp_id]
    erw [← hBσ n i]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    erw [← hAσ n i]
    simp only [Category.assoc]
    simpa only [Category.assoc] using congrArg (fun z ↦ eqToHom (eA (n + 1)) ≫ z)
      (iterate_collapse f q n i)
  have hnat := SimplexCategory.morphismProperty_eq_top
    (MorphismProperty.naturalityProperty app) (fun {_} ↦ hδ _) (fun {_} ↦ hσ _)
  exact ⟨{ app := app
           naturality := fun _ _ g ↦ by
             have h : (MorphismProperty.naturalityProperty app) g := by rw [hnat]; trivial
             exact h }, fun _ ↦ rfl⟩

private theorem modelMap_augmentation {X Y : Scheme.{v}} (f : Y ⟶ X)
    {F : X.Modules} {G : Y.Modules} (q : F ⟶ (pushforward f).obj G)
    (A : CosimplicialObject X.Modules) (B : CosimplicialObject Y.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      moduleCup_cosimplicialComplex X A)
    (b : (CochainComplex.singleFunctor Y.Modules 0).obj G ⟶
      moduleCup_cosimplicialComplex Y B)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel Y G B b)
    (g : A ⟶ B ⋙ pushforward f)
    (hg : ∀ n : SimplexCategory,
      g.app n = eqToHom (hA.choose n.len) ≫ iterate f q (n.len + 1) ≫
        (pushforward f).map (eqToHom (hB.choose n.len).symm)) :
    a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫ g.app ⦋0⦌ =
      q ≫ (pushforward f).map (b.f 0 ≫ (moduleCup_cosimplicialZeroIso Y B).hom) := by
  apply (cancel_mono ((pushforward f).map (eqToHom (hB.choose 0)))).1
  rw [hg]
  simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.comp_id]
  have ha := hA.choose_spec.2
  have hb := hB.choose_spec.2
  change a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫
    eqToHom (hA.choose 0) ≫ iterate f q 1 =
    q ≫ (pushforward f).map
      (b.f 0 ≫ (moduleCup_cosimplicialZeroIso Y B).hom ≫ eqToHom (hB.choose 0))
  erw [hb]
  rw [← Category.assoc, ← Category.assoc]
  erw [ha]
  change (𝟙 F ≫ moduleCup_godementUnit X F) ≫ lift f q =
    q ≫ (pushforward f).map (𝟙 G ≫ moduleCup_godementUnit Y G)
  simpa using lift_unit f q

private theorem sections_ext (X : Scheme.{v}) (F : X.Modules) (U : X.Opens)
    (s t : Γ(moduleCup_godementObject X F, U))
    (h : ∀ (x : X) (hx : x ∈ U), (proj X F x).app U s ⟨hx⟩ =
      (proj X F x).app U t ⟨hx⟩) : s = t := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
    CategoryTheory.forget (ModuleCat.{v} (X.ringCatSheaf.obj.obj (op U)))
  let e := asIso (piComparison E (fun x : X ↦ skyscraper x (F.presheaf.stalk x))) ≪≫
    Types.productIso (fun x ↦ E.obj (skyscraper x (F.presheaf.stalk x)))
  have coord (r : Γ(moduleCup_godementObject X F, U)) (x : X) :
      e.hom r x = (proj X F x).app U r := by
    have hh : e.hom ≫ (↾fun t ↦ t x) = E.map (proj X F x) := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      rw [Category.assoc, Types.productIso_hom_comp_eval, piComparison_comp_π]
      rfl
    exact ConcreteCategory.congr_hom hh r
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  funext x
  rw [coord, coord]
  exact SkyscraperSections.ext (h x)

private lemma exists_common_germs (X : Scheme.{v}) (H K : X.Modules) (x : X)
    (a : H.presheaf.stalk x) (c : K.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(H, U)) (r : Γ(K, U)),
      H.presheaf.germ U x hx s = a ∧ K.presheaf.germ U x hx r = c := by
  obtain ⟨U, hu, s, rfl⟩ := H.presheaf.exists_germ_eq a
  obtain ⟨V, hv, r, rfl⟩ := K.presheaf.exists_germ_eq c
  refine ⟨U ⊓ V, ⟨hu, hv⟩, H.val.map (homOfLE inf_le_left).op s,
    K.val.map (homOfLE inf_le_right).op r, ?_, ?_⟩
  · exact H.presheaf.germ_res_apply _ x _ s
  · exact K.presheaf.germ_res_apply _ x _ r

-- The common-neighbourhood calculation also allows a pairing with a general target.
-- That generality is needed when the inductive target is T^n(F₁ tensor G₁).
private theorem tensor_germs {X Y : Scheme.{v}} (f : Y ⟶ X)
    (F G : X.Modules) (F₁ G₁ H₁ : Y.Modules)
    (φ : F ⟶ (pushforward f).obj F₁) (ψ : G ⟶ (pushforward f).obj G₁)
    (χ : F ⊗ G ⟶ (pushforward f).obj H₁)
    (ℓ : F₁ ⊗ G₁ ⟶ H₁)
    (hχ : ∀ (U : X.Opens) (s : Γ(F, U)) (r : Γ(G, U)),
      χ.app U (tmulSection s r) =
        ℓ.app (f ⁻¹ᵁ U)
          (tmulSection (M := F₁) (N := G₁) (U := f ⁻¹ᵁ U) (φ.app U s) (ψ.app U r)))
    (b : ∀ H K : X.Modules, moduleCup_godementObject X H ⊗
      moduleCup_godementObject X K ⟶ moduleCup_godementObject X (H ⊗ K))
    (b₁ : ∀ H K : Y.Modules, moduleCup_godementObject Y H ⊗
      moduleCup_godementObject Y K ⟶ moduleCup_godementObject Y (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b)
    (hc₁ : ModuleCupGodementTensorCoordinates Y b₁)
    (x : Y) (s : F.presheaf.stalk (f x)) (r : G.presheaf.stalk (f x)) :
    stalk f χ x (hc.choose F G (f x) s r) =
      ℓ.stalkLinearMap x (hc₁.choose F₁ G₁ x (stalk f φ x s) (stalk f ψ x r)) := by
  obtain ⟨U, hx, s, r, rfl, rfl⟩ := exists_common_germs X F G (f x) s r
  rw [hc.choose_spec.1, stalk_germ, stalk_germ, stalk_germ, hc₁.choose_spec.1,
    Hom.stalkLinearMap_germ]
  change H₁.presheaf.germ (f ⁻¹ᵁ U) x hx (χ.app U (tmulSection s r)) =
    H₁.presheaf.germ (f ⁻¹ᵁ U) x hx (ℓ.app (f ⁻¹ᵁ U)
      (tmulSection (M := F₁) (N := G₁) (U := f ⁻¹ᵁ U) (φ.app U s) (ψ.app U r)))
  rw [hχ]

private theorem beta_apply (X : Scheme.{v})
    (b : ∀ H K : X.Modules, moduleCup_godementObject X H ⊗
      moduleCup_godementObject X K ⟶ moduleCup_godementObject X (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b)
    (F G : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(moduleCup_godementObject X F, U))
    (r : Γ(moduleCup_godementObject X G, U)) :
    (proj X (F ⊗ G) x).app U ((b F G).app U (tmulSection s r)) ⟨hx⟩ =
      hc.choose F G x ((proj X F x).app U s ⟨hx⟩) ((proj X G x).app U r ⟨hx⟩) := by
  exact hc.choose_spec.2 F G x U hx s r

private theorem lift_pairing {X Y : Scheme.{v}} (f : Y ⟶ X)
    (F G : X.Modules) (F₁ G₁ H₁ : Y.Modules)
    (φ : F ⟶ (pushforward f).obj F₁) (ψ : G ⟶ (pushforward f).obj G₁)
    (χ : F ⊗ G ⟶ (pushforward f).obj H₁)
    (ℓ : F₁ ⊗ G₁ ⟶ H₁)
    (hχ : ∀ (U : X.Opens) (s : Γ(F, U)) (r : Γ(G, U)),
      χ.app U (tmulSection s r) =
        ℓ.app (f ⁻¹ᵁ U)
          (tmulSection (M := F₁) (N := G₁) (U := f ⁻¹ᵁ U) (φ.app U s) (ψ.app U r)))
    (b : ∀ H K : X.Modules, moduleCup_godementObject X H ⊗
      moduleCup_godementObject X K ⟶ moduleCup_godementObject X (H ⊗ K))
    (b₁ : ∀ H K : Y.Modules, moduleCup_godementObject Y H ⊗
      moduleCup_godementObject Y K ⟶ moduleCup_godementObject Y (H ⊗ K))
    (hc : ModuleCupGodementTensorCoordinates X b)
    (hc₁ : ModuleCupGodementTensorCoordinates Y b₁)
    (U : X.Opens) (s : Γ(moduleCup_godementObject X F, U))
    (r : Γ(moduleCup_godementObject X G, U)) :
    (lift f χ).app U ((b F G).app U (tmulSection s r)) =
      (moduleCup_godementMap Y ℓ).app (f ⁻¹ᵁ U)
        ((b₁ F₁ G₁).app (f ⁻¹ᵁ U) (tmulSection (M := moduleCup_godementObject Y F₁)
        (N := moduleCup_godementObject Y G₁) (U := f ⁻¹ᵁ U)
        ((lift f φ).app U s) ((lift f ψ).app U r))) := by
  apply sections_ext Y H₁ (f ⁻¹ᵁ U)
  intro x hx
  rw [lift_apply, map_apply, beta_apply, beta_apply, lift_apply, lift_apply]
  exact tensor_germs f F G F₁ G₁ H₁ φ ψ χ ℓ hχ b b₁ hc hc₁ x _ _

private theorem iterate_pairing {X Y : Scheme.{v}} (f : Y ⟶ X)
    (F G : X.Modules) (F₁ G₁ : Y.Modules)
    (φ : F ⟶ (pushforward f).obj F₁) (ψ : G ⟶ (pushforward f).obj G₁)
    (χ : F ⊗ G ⟶ (pushforward f).obj (F₁ ⊗ G₁))
    (hχ : ∀ (U : X.Opens) (s : Γ(F, U)) (r : Γ(G, U)),
      χ.app U (tmulSection s r) =
        tmulSection (M := F₁) (N := G₁) (U := f ⁻¹ᵁ U) (φ.app U s) (ψ.app U r))
    (β : ModuleCupGodementBeta X) (β₁ : ModuleCupGodementBeta Y)
    (hc : ModuleCupGodementTensorCoordinates X β.map)
    (hc₁ : ModuleCupGodementTensorCoordinates Y β₁.map)
    (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗ moduleCup_godementIterate X G n ⟶
      moduleCup_godementIterate X (F ⊗ G) n)
    (p₁ : ∀ n : ℕ, moduleCup_godementIterate Y F₁ n ⊗ moduleCup_godementIterate Y G₁ n ⟶
      moduleCup_godementIterate Y (F₁ ⊗ G₁) n)
    (hp0 : p 0 = 𝟙 (F ⊗ G)) (hp₁0 : p₁ 0 = 𝟙 (F₁ ⊗ G₁))
    (hprec : ∀ n, p (n + 1) = β.map _ _ ≫ moduleCup_godementMap X (p n))
    (hp₁rec : ∀ n, p₁ (n + 1) = β₁.map _ _ ≫ moduleCup_godementMap Y (p₁ n)) :
    ∀ (n : ℕ) (U : X.Opens) (s : Γ(moduleCup_godementIterate X F n, U))
      (r : Γ(moduleCup_godementIterate X G n, U)),
      (iterate f χ n).app U ((p n).app U (tmulSection s r)) =
        (p₁ n).app (f ⁻¹ᵁ U)
          (tmulSection (M := moduleCup_godementIterate Y F₁ n)
            (N := moduleCup_godementIterate Y G₁ n) (U := f ⁻¹ᵁ U)
            ((iterate f φ n).app U s) ((iterate f ψ n).app U r)) := by
  intro n
  induction n with
  | zero =>
    intro U s r
    rw [hp0, hp₁0]
    exact hχ U s r
  | succ n ih =>
    intro U s r
    rw [hprec, hp₁rec]
    have h := lift_pairing f
      (moduleCup_godementIterate X F n) (moduleCup_godementIterate X G n)
      (moduleCup_godementIterate Y F₁ n) (moduleCup_godementIterate Y G₁ n)
      (moduleCup_godementIterate Y (F₁ ⊗ G₁) n)
      (iterate f φ n) (iterate f ψ n) (p n ≫ iterate f χ n) (p₁ n)
      ih β.map β₁.map hc hc₁ U s r
    rw [lift_precomp] at h
    exact h

end FMap

/-- Compatible augmented cosimplicial Godement f-maps and tensor pairings.
Source: Stacks Project, Tags 0FKR and 0FKU; Banerjee, arXiv:1004.1491, §1.1.4.
(blueprint: new-module-cup-godement-fmap-models)
Proof: For H → f_*H', map a stalk germ represented by s on V to the germ of its
coefficient image on f⁻¹V at x'. This defines the semilinear stalk map at x'
from the stalk at f(x'); common refinements prove independence of representatives.
The x' coordinate of the induced product-of-stalks map is the image of the
f(x') coordinate. Module linearity follows through the structure-sheaf map;
restriction forgets the same coordinates in both orders. Projection to each x'
proves compatibility with the germ unit and evaluation multiplication. Iterate
these maps and these two identities to commute with every coface and prescribed
codegeneracy. Transport through the model term equalities; equality of their
proof witnesses identifies the term equalities used for cofaces and codegeneracies.
Since these generate the simplex category, this gives the three natural
transformations. The unit identity and the model augmentation identities give
the three displayed degree-zero equations.
Choose on each scheme the coordinatewise tensor map beta of stalk skyscraper
products. Starting with p₀ = identity, define pₙ₊₁ = beta followed by T(pₙ).
The unit and multiplication laws make p commute with all insertions and collapses,
so model transport gives the two cosimplicial pairings. The unit law gives their
augmentation equations. To check the pairing square, represent the two stalk
germs on a common neighbourhood of f(x'). The hypothesis hχ on this neighbourhood
says their stalk images tensor correctly. Projection to x' proves the one-step
beta square; induction propagates it to pₙ, hence to each cosimplicial degree.
Empty products, zero sheaves and degree zero obey the same formulas. This lemma
asserts no extended-complex maps or Alexander--Whitney summand identities. -/
theorem moduleCup_godement_fmap_models (X X' : Scheme.{v}) (f : X' ⟶ X)
    [MonoidalPreadditive X.Modules] [MonoidalPreadditive X'.Modules]
    (F G : X.Modules) (F₁ G₁ : X'.Modules)
    (φ : F ⟶ (pushforward f).obj F₁) (ψ : G ⟶ (pushforward f).obj G₁)
    (χ : F ⊗ G ⟶ (pushforward f).obj (F₁ ⊗ G₁))
    (hχ : ∀ (V : X.Opens) (x : Γ(F, V)) (y : Γ(G, V)),
      χ.val.app (op V) (tmulSection x y) =
        tmulSection (φ.val.app (op V) x) (ψ.val.app (op V) y))
    (A B C : CosimplicialObject X.Modules)
      (A₁ B₁ C₁ : CosimplicialObject X'.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        moduleCup_cosimplicialComplex X A)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        moduleCup_cosimplicialComplex X B)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        moduleCup_cosimplicialComplex X C)
      (a₁ : (CochainComplex.singleFunctor X'.Modules 0).obj F₁ ⟶
        moduleCup_cosimplicialComplex X' A₁)
      (b₁ : (CochainComplex.singleFunctor X'.Modules 0).obj G₁ ⟶
        moduleCup_cosimplicialComplex X' B₁)
      (c₁ : (CochainComplex.singleFunctor X'.Modules 0).obj
        (F₁ ⊗ G₁) ⟶
        moduleCup_cosimplicialComplex X' C₁)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel X G B b)
    (hC : ModuleCupGodementModel X (F ⊗ G) C c)
    (hA₁ : ModuleCupGodementModel X' F₁ A₁ a₁)
    (hB₁ : ModuleCupGodementModel X' G₁ B₁ b₁)
    (hC₁ : ModuleCupGodementModel X'
      (F₁ ⊗ G₁) C₁ c₁)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies X G B)
    (sC : ModuleCupGodementCodegeneracies X (F ⊗ G) C)
    (sA₁ : ModuleCupGodementCodegeneracies X' F₁ A₁)
    (sB₁ : ModuleCupGodementCodegeneracies X' G₁ B₁)
    (sC₁ : ModuleCupGodementCodegeneracies X'
      (F₁ ⊗ G₁) C₁) :
    ∃ (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
      (μ₁ : moduleCup_cosimplicialTensor X' A₁ B₁ ⟶ C₁)
      (g : A ⟶ A₁ ⋙ pushforward f) (h : B ⟶ B₁ ⋙ pushforward f)
      (k : C ⟶ C₁ ⋙ pushforward f),
      ((a.f 0) ⊗ₘ (b.f 0)) ≫ moduleCup_cosimplicialZeroPair X A B C μ = c.f 0 ∧
      ((a₁.f 0) ⊗ₘ (b₁.f 0)) ≫ moduleCup_cosimplicialZeroPair X' A₁ B₁ C₁ μ₁ =
        c₁.f 0 ∧
      a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫ g.app ⦋0⦌ =
        φ ≫ (pushforward f).map (a₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' A₁).hom) ∧
      b.f 0 ≫ (moduleCup_cosimplicialZeroIso X B).hom ≫ h.app ⦋0⦌ =
        ψ ≫ (pushforward f).map (b₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' B₁).hom) ∧
      c.f 0 ≫ (moduleCup_cosimplicialZeroIso X C).hom ≫ k.app ⦋0⦌ =
        χ ≫ (pushforward f).map (c₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' C₁).hom) ∧
      ∀ (n : SimplexCategory) (V : X.Opens)
        (x : Γ(A.obj n, V)) (y : Γ(B.obj n, V)),
        (k.app n).val.app (op V) ((μ.app n).val.app (op V) (tmulSection x y)) =
          (μ₁.app n).val.app (op (f ⁻¹ᵁ V))
            (tmulSection ((g.app n).val.app (op V) x) ((h.app n).val.app (op V) y)) := by
  obtain ⟨βmap, hc⟩ := moduleCup_godement_tensor_coordinates_exists X
  obtain ⟨β₁map, hc₁⟩ := moduleCup_godement_tensor_coordinates_exists X'
  let β : ModuleCupGodementBeta X :=
    ⟨βmap, coordinates_natural X βmap hc, coordinates_unit X βmap hc,
      coordinates_multiply X βmap hc⟩
  let β₁ : ModuleCupGodementBeta X' :=
    ⟨β₁map, coordinates_natural X' β₁map hc₁, coordinates_unit X' β₁map hc₁,
      coordinates_multiply X' β₁map hc₁⟩
  obtain ⟨p, hp0, hprec, hpδ⟩ :=
    moduleCup_godement_iterate_pairings_from_beta X F G β.map β.naturality β.unit
  obtain ⟨p₁, hp₁0, hp₁rec, hp₁δ⟩ :=
    moduleCup_godement_iterate_pairings_from_beta X' F₁ G₁ β₁.map β₁.naturality β₁.unit
  have hpσ := moduleCup_godement_iterate_pairings_collapse_of_canonical
    X F G β p hp0 hprec
  have hp₁σ := moduleCup_godement_iterate_pairings_collapse_of_canonical
    X' F₁ G₁ β₁ p₁ hp₁0 hp₁rec
  obtain ⟨μ, hμ, hμ0⟩ :=
    pairingForModels X F G A B C a b c hA hB hC sA sB sC p hp0 hpδ hpσ
  obtain ⟨μ₁, hμ₁, hμ₁0⟩ :=
    pairingForModels X' F₁ G₁ A₁ B₁ C₁ a₁ b₁ c₁ hA₁ hB₁ hC₁ sA₁ sB₁ sC₁
      p₁ hp₁0 hp₁δ hp₁σ
  obtain ⟨g, hg⟩ := FMap.modelMap f φ A A₁ a a₁ hA hA₁ sA sA₁
  obtain ⟨h, hh⟩ := FMap.modelMap f ψ B B₁ b b₁ hB hB₁ sB sB₁
  obtain ⟨k, hk⟩ := FMap.modelMap f χ C C₁ c c₁ hC hC₁ sC sC₁
  refine ⟨μ, μ₁, g, h, k, hμ0, hμ₁0,
    FMap.modelMap_augmentation f φ A A₁ a a₁ hA hA₁ g hg,
    FMap.modelMap_augmentation f ψ B B₁ b b₁ hB hB₁ h hh,
    FMap.modelMap_augmentation f χ C C₁ c c₁ hC hC₁ k hk, ?_⟩
  intro n U s r
  have hpair := FMap.iterate_pairing f F G F₁ G₁ φ ψ χ hχ β β₁ hc hc₁
    p p₁ hp0 hp₁0 hprec hp₁rec (n.len + 1) U
    ((eqToHom (hA.choose n.len)).app U s) ((eqToHom (hB.choose n.len)).app U r)
  have hleft : μ.app n ≫ k.app n =
      (eqToHom (hA.choose n.len) ⊗ₘ eqToHom (hB.choose n.len)) ≫
        p (n.len + 1) ≫ FMap.iterate f χ (n.len + 1) ≫
          (pushforward f).map (eqToHom (hC₁.choose n.len).symm) := by
    rw [hμ n, hk n]
    simp only [Category.assoc]
    have he : eqToHom (hC.choose n.len).symm ≫ eqToHom (hC.choose n.len) ≫
        FMap.iterate f χ (n.len + 1) ≫
          (pushforward f).map (eqToHom (hC₁.choose n.len).symm) =
        FMap.iterate f χ (n.len + 1) ≫
          (pushforward f).map (eqToHom (hC₁.choose n.len).symm) := by
      rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact congrArg (fun (z : moduleCup_godementIterate X (F ⊗ G) (n.len + 1) ⟶
        (pushforward f).obj (C₁.obj n)) ↦
      ((eqToHom (hA.choose n.len) ⊗ₘ eqToHom (hB.choose n.len)) ≫ p (n.len + 1) ≫ z :
        A.obj n ⊗ B.obj n ⟶ (pushforward f).obj (C₁.obj n))) he
  have hg' : (eqToHom (hA₁.choose n.len)).app (f ⁻¹ᵁ U) ((g.app n).app U s) =
      (FMap.iterate f φ (n.len + 1)).app U ((eqToHom (hA.choose n.len)).app U s) := by
    change ((g.app n ≫ (pushforward f).map (eqToHom (hA₁.choose n.len))).app U s) =
      ((eqToHom (hA.choose n.len) ≫ FMap.iterate f φ (n.len + 1)).app U s)
    erw [hg n]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
  have hh' : (eqToHom (hB₁.choose n.len)).app (f ⁻¹ᵁ U) ((h.app n).app U r) =
      (FMap.iterate f ψ (n.len + 1)).app U ((eqToHom (hB.choose n.len)).app U r) := by
    change ((h.app n ≫ (pushforward f).map (eqToHom (hB₁.choose n.len))).app U r) =
      ((eqToHom (hB.choose n.len) ≫ FMap.iterate f ψ (n.len + 1)).app U r)
    erw [hh n]
    simp only [Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
    erw [CategoryTheory.Functor.map_id]
    rw [Category.comp_id]
  change (μ.app n ≫ k.app n).app U (tmulSection s r) =
    (μ₁.app n).app (f ⁻¹ᵁ U)
      (tmulSection (M := A₁.obj n) (N := B₁.obj n) (U := f ⁻¹ᵁ U)
        ((g.app n).app U s) ((h.app n).app U r))
  rw [hleft, hμ₁ n]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app]
  have ht := tensorHom_app_tmulSection
    (eqToHom (hA.choose n.len)) (eqToHom (hB.choose n.len)) s r
  have ht₁ := tensorHom_app_tmulSection
    (eqToHom (hA₁.choose n.len)) (eqToHom (hB₁.choose n.len))
    ((g.app n).app U s) ((h.app n).app U r)
  erw [ht, ht₁]
  rw [hg', hh']
  exact congrArg ((eqToHom (hC₁.choose n.len).symm).app (f ⁻¹ᵁ U)) hpair


end
end AlgebraicGeometry.Scheme.Modules
