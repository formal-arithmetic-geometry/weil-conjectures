/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Mathlib.CategoryTheory.Functor.OfSequence
import Sheaf.Paper.KFlatRingedToposPullback

/-! # K-flat realization of the augmented scalar-extension tower

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0D6D and 07A6
(blueprint: lem-pe-kflat-scalar-tower-realization).

Indices are shifted by one: Lean index zero denotes the paper's first coefficient.
`localize` is the standard localization through the homotopy quotient. Its canonical
comparison with `DerivedCategory.Q` is `DerivedCategory.quotientCompQhIso`.
All constructions use the dependency's fixed ordinary and derived presentations.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

universe u v r w uA vA
open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.KFlatScalarTower
open SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]
  (p : ∀ {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S), Presentation a)
  (N : Normalization p)

/-- The ordinary extension followed by restriction, using the existing tensor.
Source: Stacks 06YY (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev ordinaryEnd {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :=
  (p a).ordinary ⋙ restriction a

/-- The derived extension followed by exact restriction.
Source: Stacks 06YY, 07A6 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev derivedEnd {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :=
  (p a).derived ⋙ N.right a

/-- Localization of actual cochain complexes through the homotopy quotient.
Source: Stacks 05RR (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable abbrev localize (R : Sheaf J CommRingCat.{r}) :=
  HomotopyCategory.quotient (Modules R) (.up ℤ) ⋙ DerivedCategory.Qh

/-- The strict coefficient transition: the ordinary adjoint of scalar composition,
followed by restriction and the identity-on-sections restriction comparison.
Source: Stacks 03EK, 07A6, 0D6D
(blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def ordinaryStep {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') :
    ordinaryEnd p a ⟶ ordinaryEnd p a' :=
  Functor.whiskerRight
    (Functor.whiskerLeft (p a).ordinary (N.ordinaryAdjunction b).unit ≫
      Functor.whiskerRight ((N.ordinary a b).hom ≫
        eqToHom (congrArg (fun f ↦ (p f).ordinary) h)) (restriction b))
    (restriction a) ≫
  Functor.whiskerLeft (p a').ordinary ((N.restrictionComp a b).hom ≫
    eqToHom (congrArg (fun f ↦ restriction f) h))

/-- The derived transition is the adjoint of the specified scalar-composition map,
then restricted and identified by the underlying-sheaf comparison.
Source: Stacks 07A6, 0D6D (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def derivedStep {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') :
    derivedEnd p N a ⟶ derivedEnd p N a' :=
  Functor.whiskerRight
    (Functor.whiskerLeft (p a).derived (N.adjunction b).unit ≫
      Functor.whiskerRight ((N.derived a b).hom ≫
        eqToHom (congrArg (fun f ↦ (p f).derived) h)) (N.right b))
    (N.right a) ≫
  Functor.whiskerLeft (p a').derived ((N.rightComp a b).hom ≫
    eqToHom (congrArg (fun f ↦ N.right f) h))

/-- The canonical K-flat computation morphism after restriction. No arbitrary
isomorphism is chosen: this is the universal derived counit and its factorization.
Source: Stacks 06YY, 07A6 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def computation {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) :
    (derivedEnd p N a).obj ((localize R).obj P) ⟶
      (localize R).obj (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).obj P) :=
  (N.right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
    (N.right_factors a).hom.app
      (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj P)) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (ordinaryEnd p a)) (.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ _).obj P))

/-- Transport of the canonical computation along the inverse representative isomorphism.
Source: Stacks 06YY (blueprint: lem-pe-kflat-scalar-tower-realization). -/
noncomputable def epsilon {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) (K : DerivedCategory (Modules R))
    (e : (localize R).obj P ≅ K) :
    (derivedEnd p N a).obj K ⟶
      (localize R).obj (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).obj P) :=
  (derivedEnd p N a).map e.inv ≫ computation p N a P

/-- Finite composites in any inverse sequence, including the empty composite.
This is Mathlib's inverse-sequence functor, with its order morphism evaluated.
Source: Stacks 00D3 (blueprint: lem-pe-kflat-scalar-tower-realization). -/
def composite {A : Type uA} [Category.{vA} A] {X : ℕ → A}
    (f : ∀ n : ℕ, X (n + 1) ⟶ X n) (n m : ℕ) (h : n ≤ m) : X m ⟶ X n :=
  (Functor.ofOpSequence f).map (homOfLE h).op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_tensor_ext {A R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (c : A ⟶ S) (M : Modules R) (H : Modules A)
    (f g : (restriction c).obj ((p a).ordinary.obj M) ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (sectionTensor (p a) M U s x) =
        g.val.app U (sectionTensor (p a) M U s x)) : f = g := by
  let j := (restriction c).map (eqToHom ((p a).obj_eq M).symm)
  apply (cancel_epi j).mp
  apply (toSheaf _).map_injective
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ H.isSheaf
  ext U z
  let : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (a.hom.app U).hom
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul s x => exact h U s x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryStep_sections {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((ordinaryStep p N a b a' h).app M).val.app U (sectionTensor (p a) M U s x) =
      sectionTensor (p a') M U ((b.hom.app U).hom s) x := by
  subst a'
  change ((N.restrictionComp a b).hom.app _).val.app U
    (((N.ordinary a b).hom.app M).val.app U
      (((N.ordinaryAdjunction b).unit.app _).val.app U (sectionTensor (p a) M U s x))) = _
  rw [N.restrictionComp_sections, N.ordinary_unit, N.ordinary_hom, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryStep_unit {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a') (M : Modules R) :
    (N.ordinaryAdjunction a).unit.app M ≫ (ordinaryStep p N a b a' h).app M =
      (N.ordinaryAdjunction a').unit.app M := by
  ext U x
  change ((ordinaryStep p N a b a' h).app M).val.app U
    (((N.ordinaryAdjunction a).unit.app M).val.app U x) = _
  rw [N.ordinary_unit, ordinaryStep_sections, map_one, ← N.ordinary_unit]

-- Keeping the restriction in the section's type avoids repeatedly comparing
-- the scalar-action records for the original and restricted modules.
private noncomputable def restrictedSection {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((ordinaryEnd p a).obj M).val.obj U := sectionTensor (p a) M U s x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictedSection_step {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (M : Modules R) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((ordinaryStep p N a b a' h).app M).val.app U (restrictedSection p a M U s x) =
      restrictedSection p a' M U ((b.hom.app U).hom s) x :=
  ordinaryStep_sections p N a b a' h M U s x

private theorem restrictedSection_ext {R S : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (M H : Modules R) (f g : (ordinaryEnd p a).obj M ⟶ H)
    (h : ∀ (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
      f.val.app U (restrictedSection p a M U s x) =
        g.val.app U (restrictedSection p a M U s x)) : f = g :=
  restricted_tensor_ext p a a M H f g h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryStep_id {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (M : Modules R) :
    (ordinaryStep p N a (𝟙 S) a (Category.comp_id a)).app M = 𝟙 _ := by
  apply restrictedSection_ext p a M _
  intro U s x
  rw [restrictedSection_step]
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryStep_comp {R S T V : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V) (a' : R ⟶ T) (a'' : R ⟶ V)
    (h : a ≫ b = a') (h' : a' ≫ c = a'') (hc : a ≫ (b ≫ c) = a'') :
    ordinaryStep p N a (b ≫ c) a'' hc =
      ordinaryStep p N a b a' h ≫ ordinaryStep p N a' c a'' h' := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app]
  apply restrictedSection_ext p a M _
  intro U s x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  rw [restrictedSection_step, restrictedSection_step, restrictedSection_step]
  rfl

private theorem composite_refl {A : Type uA} [Category.{vA} A] {X : ℕ → A}
    (f : ∀ n : ℕ, X (n + 1) ⟶ X n) (n : ℕ) :
    composite f n n (le_refl n) = 𝟙 _ := by
  exact (Functor.ofOpSequence f).map_id _

private theorem composite_succ {A : Type uA} [Category.{vA} A] {X : ℕ → A}
    (f : ∀ n : ℕ, X (n + 1) ⟶ X n) (n m : ℕ) (h : n ≤ m) :
    composite f n (m + 1) (h.trans (Nat.le_succ m)) = f m ≫ composite f n m h := by
  have hcomp := (Functor.ofOpSequence f).map_comp
    (homOfLE (Nat.le_succ m)).op (homOfLE h).op
  simpa only [← op_comp, homOfLE_comp, composite,
    Functor.ofOpSequence_map_homOfLE_succ] using hcomp

private theorem composite_square {A : Type uA} [Category.{vA} A]
    {D : Type u} [Category.{v} D] (L : A ⥤ D) {X : ℕ → D} {Y : ℕ → A}
    (f : ∀ n, X (n + 1) ⟶ X n) (g : ∀ n, Y (n + 1) ⟶ Y n)
    (eps : ∀ n, X n ⟶ L.obj (Y n))
    (h : ∀ n, f n ≫ eps n = eps (n + 1) ≫ L.map (g n))
    (n m : ℕ) (hnm : n ≤ m) :
    composite f n m hnm ≫ eps n = eps m ≫ L.map (composite g n m hnm) := by
  let τ : Functor.ofOpSequence f ⟶ Functor.ofOpSequence g ⋙ L :=
    NatTrans.ofOpSequence eps (by
      intro i
      simpa only [Functor.ofOpSequence_map_homOfLE_succ, Functor.comp_map] using h i)
  exact τ.naturality (homOfLE hnm).op

private theorem coefficient_composite {R : Sheaf J CommRingCat.{r}}
    (B : ℕ → Sheaf J CommRingCat.{r}) (a : ∀ n, R ⟶ B n)
    (b : ∀ n, B (n + 1) ⟶ B n) (h : ∀ n, a (n + 1) ≫ b n = a n)
    (n m : ℕ) (hnm : n ≤ m) : a m ≫ composite b n m hnm = a n := by
  let τ : (Functor.const ℕᵒᵖ).obj R ⟶ Functor.ofOpSequence b :=
    NatTrans.ofOpSequence a (by
      intro i
      rw [Functor.const_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
      exact (Category.id_comp _).trans (h i).symm)
  exact (τ.naturality (homOfLE hnm).op).symm.trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryStep_composite {R : Sheaf J CommRingCat.{r}}
    (B : ℕ → Sheaf J CommRingCat.{r}) (a : ∀ n, R ⟶ B n)
    (b : ∀ n, B (n + 1) ⟶ B n) (h : ∀ n, a (n + 1) ≫ b n = a n)
    (P : CochainComplex (Modules R) ℤ) (n m : ℕ) (hnm : n ≤ m)
    (hc : a m ≫ composite b n m hnm = a n) :
    (NatTrans.mapHomologicalComplex (ordinaryStep p N (a m) (composite b n m hnm)
      (a n) hc) (.up ℤ)).app P =
      composite (X := fun i ↦ ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
        (fun i ↦ (NatTrans.mapHomologicalComplex
          (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P) n m hnm := by
  revert hc
  induction m, hnm using Nat.le_induction with
  | base =>
      intro hc
      simp only [composite_refl]
      ext i : 1
      exact ordinaryStep_id p N (a n) (P.X i)
  | succ m hnm ih =>
      intro hc
      rw [composite_succ (X := fun i ↦
        ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
        (fun i ↦ (NatTrans.mapHomologicalComplex
        (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P) n m hnm]
      rw [← ih (coefficient_composite B a b h n m hnm)]
      have hs := ordinaryStep_comp p N (a (m + 1)) (b m) (composite b n m hnm)
        (a m) (a n) (h m) (coefficient_composite B a b h n m hnm)
        (by rw [← Category.assoc, h m, coefficient_composite B a b h n m hnm])
      simp only [composite_succ b n m hnm]
      rw [hs, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem computation_eq {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ) :
    computation p N a P =
      (N.right a).map ((p a).counit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
        (N.right_factors a).hom.app
          (((p a).ordinary.mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj P)) := by
  change _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilon_isIso {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i))
    (K : DerivedCategory (Modules R)) (e : (localize R).obj P ≅ K) :
    IsIso (epsilon p N a P K e) := by
  have := N.computed a P hP hf
  dsimp [epsilon, computation]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem computation_unit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i)) :
    (N.adjunction a).unit.app ((localize R).obj P) ≫ computation p N a P =
      (localize R).map
        ((NatTrans.mapHomologicalComplex (N.ordinaryAdjunction a).unit (.up ℤ)).app P) := by
  have hunit : ((N.ordinaryAdjunction a).mapHomologicalComplex (.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction a).unit (.up ℤ)).app P := by
    ext i : 1
    exact Adjunction.mapHomologicalComplex_unit_app_f (.up ℤ) (N.ordinaryAdjunction a) P i
  rw [computation_eq]
  simpa only [Adjunction.mapHomotopyCategory_unit_app_quotient, hunit, localize,
    Functor.comp_obj, Functor.comp_map] using N.adjunction_normalization a P hP hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilon_unit {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i))
    (K : DerivedCategory (Modules R)) (e : (localize R).obj P ≅ K) :
    e.hom ≫ (N.adjunction a).unit.app K ≫ epsilon p N a P K e =
      (localize R).map
        ((NatTrans.mapHomologicalComplex (N.ordinaryAdjunction a).unit (.up ℤ)).app P) := by
  dsimp only [epsilon, derivedEnd]
  erw [← Category.assoc, (N.adjunction a).unit.naturality e.hom]
  rw [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact computation_unit p N a P hP hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem computation_naturality {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    {P P' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') :
    (derivedEnd p N a).map ((localize R).map f) ≫ computation p N a P' =
      computation p N a P ≫ (localize R).map
        (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).map f) := by
  let E := (p a).ordinary.mapHomotopyCategory (.up ℤ)
  let τ : DerivedCategory.Qh ⋙ derivedEnd p N a ⟶
      E ⋙ (restriction a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.whiskerRight (p a).counit (N.right a) ≫
      Functor.whiskerLeft E (N.right_factors a).hom
  rw [computation_eq, computation_eq]
  exact τ.naturality ((HomotopyCategory.quotient (Modules R) (.up ℤ)).map f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilon_naturality {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
    {P P' : CochainComplex (Modules R) ℤ}
    {K K' : DerivedCategory (Modules R)} (e : (localize R).obj P ≅ K)
    (e' : (localize R).obj P' ≅ K') (f : P ⟶ P') (g : K ⟶ K')
    (h : (localize R).map f ≫ e'.hom = e.hom ≫ g) :
    (derivedEnd p N a).map g ≫ epsilon p N a P' K' e' =
      epsilon p N a P K e ≫ (localize R).map
        (((ordinaryEnd p a).mapHomologicalComplex (.up ℤ)).map f) := by
  have he : g ≫ e'.inv = e.inv ≫ (localize R).map f := by
    rw [← cancel_mono e'.hom]
    simpa [Category.assoc, h] using congrArg (fun k ↦ e.inv ≫ k) h.symm
  dsimp only [epsilon]
  rw [← Category.assoc, ← Functor.map_comp, he, Functor.map_comp, Category.assoc,
    computation_naturality p N a f]
  simp only [Category.assoc]

private noncomputable def identityInverse (R : Sheaf J CommRingCat.{r}) :
    AlgebraicInverseImage (𝟭 (Sheaf J (Type r))) R R where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 (Modules R)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem computation_step {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i)) :
    (derivedStep p N a b a' h).app ((localize R).obj P) ≫ computation p N a' P =
      computation p N a P ≫ (localize R).map
        ((NatTrans.mapHomologicalComplex (ordinaryStep p N a b a' h) (.up ℤ)).app P) := by
  subst a'
  let H := (HomotopyCategory.quotient (Modules R) (.up ℤ)).obj P
  let E := (p a).ordinary.mapHomotopyCategory (.up ℤ)
  have hE := isKFlat_ringedToposPullback (𝟭 _) (𝟭 _) Adjunction.id
    (identityInverse R) a (p a).ordinary (p a).obj_eq (p a).map_eq P hP hf
  have hu := N.adjunction_normalization b
    (((p a).ordinary.mapHomologicalComplex (.up ℤ)).obj P) hE.1 hE.2
  have hp := N.representative a b P hP hf
  have hn := (N.rightComp a b).hom.naturality ((p (a ≫ b)).counit.app H)
  have hfactors := N.rightComp_normalization a b
    (((p (a ≫ b)).ordinary.mapHomotopyCategory (.up ℤ)).obj H)
  have hp' := congrArg (fun k ↦ (N.right a).map ((N.right b).map k)) hp
  simp only [Functor.map_comp] at hp'
  have hun := (N.adjunction b).unit.naturality ((p a).counit.app H)
  dsimp only [Functor.id_map, Functor.comp_map] at hun
  have hun' := congrArg (fun k ↦ (N.right a).map k) hun
  simp only [Functor.map_comp] at hun'
  simp only [computation_eq]
  simp only [derivedStep, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, eqToHom_refl, Category.comp_id, Functor.map_comp,
    Category.assoc]
  erw [reassoc_of% hn.symm, reassoc_of% hp', ← reassoc_of% hun']
  erw [hfactors]
  let δ := (Functor.mapHomotopyCategoryCompIso (N.ordinary a b) (.up ℤ)).hom.app H
  have hrb := (N.right_factors b).hom.naturality δ
  have hrb' := congrArg (fun k ↦ (N.right a).map k) hrb
  simp only [Functor.comp_map, Functor.map_comp] at hrb'
  erw [reassoc_of% hrb']
  have hu' := congrArg (fun k ↦ (N.right a).map k) hu
  simp only [Functor.map_comp] at hu'
  erw [reassoc_of% hu']
  let η := ((N.ordinaryAdjunction b).mapHomotopyCategory (.up ℤ)).unit.app (E.obj H)
  have hraδ := (N.right_factors a).hom.naturality
    (((restriction b).mapHomotopyCategory (.up ℤ)).map δ)
  have hraη := (N.right_factors a).hom.naturality η
  dsimp only [Functor.comp_map] at hraδ hraη
  erw [reassoc_of% hraδ, reassoc_of% hraη]
  dsimp only [localize, Functor.comp_map]
  simp only [← DerivedCategory.Qh.map_comp]
  apply congrArg (fun k ↦ (N.right a).map ((p a).counit.app H) ≫
    (N.right_factors a).hom.app (E.obj H) ≫ DerivedCategory.Qh.map k)
  dsimp only [η, δ, E, H]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _ =
    (HomotopyCategory.quotient (Modules R) (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem epsilon_step {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) (a' : R ⟶ T) (h : a ≫ b = a')
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i))
    (K : DerivedCategory (Modules R)) (e : (localize R).obj P ≅ K) :
    (derivedStep p N a b a' h).app K ≫ epsilon p N a' P K e =
      epsilon p N a P K e ≫ (localize R).map
        ((NatTrans.mapHomologicalComplex (ordinaryStep p N a b a' h) (.up ℤ)).app P) := by
  dsimp only [epsilon]
  rw [← Category.assoc, ← (derivedStep p N a b a' h).naturality e.inv,
    Category.assoc, computation_step p N a b a' h P hP hf]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The augmented K-flat realization, including its prescribed computation maps,
strict tensor formulas, naturality and compatibility with all finite transitions.
There is no flatness/surjectivity assumption on coefficient maps and no boundedness.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0D6D, 0G7E and 07A6
(blueprint: lem-pe-kflat-scalar-tower-realization).

Proof:
1. The ordinary mate defining ordinaryStep sends a pure tensor s tensor x to
b(s) tensor x. Balancing uses a followed by b equals a'; restriction is the identity
on underlying sheaves. Sectionwise maps descend through sheafification and commute
with differentials. The ordinary adjunction unit is x mapped to 1 tensor x.
2. Apply lem-pur-derived-change-of-rings to a flat-term K-flat P. The canonical
counit is invertible. Exact restriction and its localization factorization give
computation. Transport by the inverse of e gives epsilon, also invertible.
3. The normalized unit clause of lem-pur-sheaf-ring-derived-coefficient-adjunction
identifies the unit on P with its strict ordinary unit. Naturality at e gives the
augmentation equation below.
4. By lem-weil-pbc-ringed-topos-kflat-pullback, extension along a preserves flat-term
K-flatness. The representative clause of
lem-sfb-successive-derived-quotient-normalization identifies scalar composition
with t tensor (s tensor x) mapped to b(s)t tensor x, in scalar-first notation.
5. The adjoint is restriction of that comparison after the normalized unit for b;
it therefore sends s tensor x to b(s) tensor x. Restricting gives the adjacent
transition equation, and naturality transports it along e.
6. Naturality of the universal counit and all factorization comparisons gives the
square for every chain map f, and hence for transported representatives and g.
Compose adjacent equalities to obtain the finite-transition equation, including
identities. The coherent iterated comparisons of the normalization dependency
identify these composites with the direct mate for the composite ring map.
This also proves compatibility of the augmentations and the ring-map composites. -/
theorem kflat_scalar_tower_realization
    {R : Sheaf J CommRingCat.{r}} (B : ℕ → Sheaf J CommRingCat.{r})
    (a : ∀ n : ℕ, R ⟶ B n) (b : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (h : ∀ n : ℕ, a (n + 1) ≫ b n = a n)
    (P : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hf : ∀ i : ℤ, IsFlatOnSite (R := R) (P.X i))
    (K : DerivedCategory (Modules R)) (e : (localize R).obj P ≅ K) :
    (∀ n : ℕ, IsIso (epsilon p N (a n) P K e)) ∧
    (∀ n : ℕ, e.hom ≫ (N.adjunction (a n)).unit.app K ≫
      epsilon p N (a n) P K e =
      (localize R).map
        ((NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a n)).unit (.up ℤ)).app P)) ∧
    (∀ n : ℕ, (derivedStep p N (a (n + 1)) (b n) (a n) (h n)).app K ≫
      epsilon p N (a n) P K e = epsilon p N (a (n + 1)) P K e ≫
        (localize R).map ((NatTrans.mapHomologicalComplex
          (ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)) (.up ℤ)).app P)) ∧
    (∀ (n : ℕ) (i : ℤ) (U : Cᵒᵖ) (s : (B (n + 1)).obj.obj U)
      (x : (P.X i).val.obj U),
      ((ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)).app (P.X i)).val.app U
        (sectionTensor (p (a (n + 1))) (P.X i) U s x) =
      sectionTensor (p (a n)) (P.X i) U (((b n).hom.app U).hom s) x) ∧
    (∀ n : ℕ,
      (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a (n + 1))).unit
        (.up ℤ)).app P ≫
      (NatTrans.mapHomologicalComplex
        (ordinaryStep p N (a (n + 1)) (b n) (a n) (h n)) (.up ℤ)).app P =
      (NatTrans.mapHomologicalComplex (N.ordinaryAdjunction (a n)).unit (.up ℤ)).app P) ∧
    (∀ (P' : CochainComplex (Modules R) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (R := R) P' →
      (∀ i : ℤ, IsFlatOnSite (R := R) (P'.X i)) →
      ∀ (K' : DerivedCategory (Modules R)) (e' : (localize R).obj P' ≅ K')
        (f : P ⟶ P') (g : K ⟶ K'), (localize R).map f ≫ e'.hom = e.hom ≫ g →
      ∀ n : ℕ, (derivedEnd p N (a n)).map g ≫ epsilon p N (a n) P' K' e' =
        epsilon p N (a n) P K e ≫ (localize R).map
          (((ordinaryEnd p (a n)).mapHomologicalComplex (.up ℤ)).map f)) ∧
    (∀ (n m : ℕ) (hnm : n ≤ m),
      composite (X := fun i ↦ (derivedEnd p N (a i)).obj K)
        (fun i ↦ (derivedStep p N (a (i + 1)) (b i) (a i) (h i)).app K)
        n m hnm ≫ epsilon p N (a n) P K e =
      epsilon p N (a m) P K e ≫ (localize R).map
        (composite (X := fun i ↦
          ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
          (fun i ↦ (NatTrans.mapHomologicalComplex
            (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P) n m hnm)) ∧
    (∀ (n m : ℕ) (hnm : n ≤ m),
      ∃ hc : a m ≫ composite (X := B) b n m hnm = a n,
        ((derivedStep p N (a m) (composite (X := B) b n m hnm) (a n) hc).app K =
          composite (X := fun i ↦ (derivedEnd p N (a i)).obj K)
            (fun i ↦ (derivedStep p N (a (i + 1)) (b i) (a i) (h i)).app K)
            n m hnm) ∧
        ((NatTrans.mapHomologicalComplex
          (ordinaryStep p N (a m) (composite (X := B) b n m hnm) (a n) hc)
          (.up ℤ)).app P =
          composite (X := fun i ↦
            ((ordinaryEnd p (a i)).mapHomologicalComplex (.up ℤ)).obj P)
            (fun i ↦ (NatTrans.mapHomologicalComplex
              (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P)
            n m hnm)) := by
  have hadj (n : ℕ) := epsilon_step p N (a (n + 1)) (b n) (a n) (h n) P hP hf K e
  have hfinite (n m : ℕ) (hnm : n ≤ m) :=
    composite_square (localize R)
      (fun i ↦ (derivedStep p N (a (i + 1)) (b i) (a i) (h i)).app K)
      (fun i ↦ (NatTrans.mapHomologicalComplex
        (ordinaryStep p N (a (i + 1)) (b i) (a i) (h i)) (.up ℤ)).app P)
      (fun i ↦ epsilon p N (a i) P K e) hadj n m hnm
  refine ⟨fun n ↦ epsilon_isIso p N (a n) P hP hf K e,
    fun n ↦ epsilon_unit p N (a n) P hP hf K e, hadj,
    fun n i U s x ↦ ordinaryStep_sections p N (a (n + 1)) (b n) (a n) (h n)
      (P.X i) U s x, ?_,
    fun P' _ _ K' e' f g he n ↦ epsilon_naturality p N (a n) e e' f g he,
    hfinite, ?_⟩
  · intro n
    ext i : 1
    exact ordinaryStep_unit p N (a (n + 1)) (b n) (a n) (h n) (P.X i)
  · intro n m hnm
    let hc := coefficient_composite B a b h n m hnm
    refine ⟨hc, ?_, ordinaryStep_composite p N B a b h P n m hnm hc⟩
    have := epsilon_isIso p N (a n) P hP hf K e
    apply (cancel_mono (epsilon p N (a n) P K e)).1
    rw [epsilon_step p N (a m) (composite b n m hnm) (a n) hc P hP hf K e,
      ordinaryStep_composite p N B a b h P n m hnm hc]
    exact (hfinite n m hnm).symm

end SheafOfModules.KFlatScalarTower
