/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ, Bin Wu, SHEAF group Z7
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Mathlib.Algebra.Homology.Refinements
import WeilConjectures.Algebra.Homology.CyclePullbackLifting

/-!
# Bounded-above resolutions from a quotient-generating class

Source: Stacks Project, Derived Categories, Tag 05T7,
`derived-lemma-subcategory-left-resolution`, part (1)
(blueprint: lem-sfb-subcategory-left-resolution).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

namespace SubcategoryResolution

-- Objectwise specialization of the explicit Stacks 05T7 tower in
-- WeilConjectures.Algebra.Homology.CyclePullbackTower, CyclePullbackLaws, and
-- CyclePullbackTowerComparison. The chosen covers need not extend to a functor.

variable {A : Type u} [Category.{v} A] [Abelian A]

private def targetTerm (F : CochainComplex A ℤ) (i : ℤ) : A :=
  F.X i

private def targetD (F : CochainComplex A ℤ) (i j : ℤ) :
    targetTerm F i ⟶ targetTerm F j :=
  F.d i j

-- Retain exactly the two adjacent terms needed by the next descending step.
private structure Stage (F : CochainComplex A ℤ) where
  degree : ℤ
  current : A
  next : A
  d : current ⟶ next
  e : current ⟶ targetTerm F degree

private noncomputable def initial (Z : A) (F : CochainComplex A ℤ) (N : ℤ) : Stage F where
  degree := N + 1
  current := Z
  next := Z
  d := 0
  e := 0

private noncomputable def cyclesArrow {F : CochainComplex A ℤ} (s : Stage F) :
    kernel s.d ⟶ targetTerm F s.degree := kernel.ι s.d ≫ s.e

private noncomputable def stepPullback {F : CochainComplex A ℤ} (s : Stage F) : A :=
  pullback (targetD F (s.degree - 1) s.degree) (cyclesArrow s)

private noncomputable def step (_Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {F : CochainComplex A ℤ} (s : Stage F) : Stage F where
  degree := s.degree - 1
  current := T (stepPullback s)
  next := s.current
  d := π (stepPullback s) ≫
    pullback.snd (targetD F (s.degree - 1) s.degree) (cyclesArrow s) ≫ kernel.ι s.d
  e := π (stepPullback s) ≫
    pullback.fst (targetD F (s.degree - 1) s.degree) (cyclesArrow s)

-- Covers are chosen objectwise; no functoriality or closure of P is assumed.
private noncomputable def tower (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N : ℤ) : ℕ → Stage F
  | 0 => initial Z F N
  | k + 1 => step Z T π (tower Z T π F N k)

private theorem tower_degree (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N : ℤ) (k : ℕ) :
    (tower Z T π F N k).degree = N + 1 - (k : ℤ) := by
  induction k with
  | zero => simp [tower, initial]
  | succ k hk => simp only [tower, step, hk, Nat.cast_add, Nat.cast_one]; omega

private def depth (N i : ℤ) : ℕ := (N - i).toNat + 1

-- Each integer degree uses its permanently assigned term in the natural-number tower.
private noncomputable def term (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) : A :=
  if i ≤ N then (tower Z T π F N (depth N i)).current else Z

private theorem tower_next (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    (tower Z T π F N (depth N i)).next = term Z T π F N (i + 1) := by
  by_cases h : i = N
  · subst i
    simp [depth, tower, step, initial, term]
  · have h' : i + 1 ≤ N := by omega
    have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
    rw [hd]
    simp only [tower, step, term, if_pos h']

private theorem term_eq (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    term Z T π F N i = (tower Z T π F N (depth N i)).current := by
  simp only [term, if_pos hi]

private theorem degree_eq (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    (tower Z T π F N (depth N i)).degree = i := by
  rw [tower_degree]
  unfold depth
  omega

private noncomputable def differential (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) :
    term Z T π F N i ⟶ term Z T π F N (i + 1) :=
  if hi : i ≤ N then
    eqToHom (term_eq Z T π F N i hi) ≫ (tower Z T π F N (depth N i)).d ≫
      eqToHom (tower_next Z T π F N i hi)
  else 0

private noncomputable def augmentation (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) :
    term Z T π F N i ⟶ targetTerm F i :=
  if hi : i ≤ N then
    eqToHom (term_eq Z T π F N i hi) ≫ (tower Z T π F N (depth N i)).e ≫
      eqToHom (congrArg (targetTerm F) (degree_eq Z T π F N i hi))
  else 0

private theorem step_square (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {F : CochainComplex A ℤ} (s : Stage F) :
    (step Z T π s).d ≫ s.d = 0 := by
  simp only [step, Category.assoc, kernel.condition, comp_zero]

private theorem step_comm (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {F : CochainComplex A ℤ} (s : Stage F) :
    (step Z T π s).e ≫ targetD F (s.degree - 1) s.degree = (step Z T π s).d ≫ s.e := by
  dsimp only [step]
  rw [Category.assoc, pullback.condition]
  simp only [cyclesArrow, Category.assoc]

-- Transport the kernel and pullback equations to the integer-indexed maps.
private theorem pair_square (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {F : CochainComplex A ℤ} (s t : Stage F) (h : s = step Z T π t) :
    s.d ≫ eqToHom (show s.next = t.current from by rw [h]; rfl) ≫ t.d = 0 := by
  subst s
  simpa using step_square Z T π t

private theorem pair_comm (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {F : CochainComplex A ℤ} (s t : Stage F) (h : s = step Z T π t) :
    s.e ≫ targetD F s.degree t.degree =
      s.d ≫ eqToHom (show s.next = t.current from by rw [h]; rfl) ≫ t.e := by
  subst s
  simpa only [step, eqToHom_refl, Category.id_comp] using step_comm Z T π t

private theorem target_transport (F : CochainComplex A ℤ)
    (a b i j : ℤ) (ha : a = i) (hb : b = j) :
    eqToHom (congrArg (targetTerm F) ha) ≫ targetD F i j =
      targetD F a b ≫ eqToHom (congrArg (targetTerm F) hb) := by
  subst i j
  simp

private theorem square_below (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i < N) :
    differential Z T π F N i ≫ differential Z T π F N (i + 1) = 0 := by
  have hi' : i ≤ N := by omega
  have hn : i + 1 ≤ N := by omega
  have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
  have hs : tower Z T π F N (depth N i) = step Z T π (tower Z T π F N (depth N (i + 1))) := by
    rw [hd]; rfl
  have h := pair_square Z T π _ _ hs
  dsimp only [differential]
  rw [dif_pos hi', dif_pos hn]
  simp only [Category.assoc, eqToHom_trans_assoc]
  have h' := congrArg (fun f ↦ eqToHom (term_eq Z T π F N i hi') ≫ f ≫
    eqToHom (tower_next Z T π F N (i + 1) hn)) h
  simpa only [Category.assoc, comp_zero, zero_comp] using h'

private theorem comm_below (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i < N) :
    augmentation Z T π F N i ≫ targetD F i (i + 1) =
      differential Z T π F N i ≫ augmentation Z T π F N (i + 1) := by
  have hi' : i ≤ N := by omega
  have hn : i + 1 ≤ N := by omega
  have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
  have hs : tower Z T π F N (depth N i) = step Z T π (tower Z T π F N (depth N (i + 1))) := by
    rw [hd]; rfl
  have h := pair_comm Z T π _ _ hs
  dsimp only [differential, augmentation]
  rw [dif_pos hi', dif_pos hn, dif_pos hi']
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [target_transport F _ _ i (i + 1) (degree_eq Z T π F N i hi')
    (degree_eq Z T π F N (i + 1) hn)]
  have h' := congrArg (fun f ↦ eqToHom (term_eq Z T π F N i hi') ≫ f ≫
    eqToHom (congrArg (targetTerm F) (degree_eq Z T π F N (i + 1) hn))) h
  simpa only [Category.assoc] using h'

private theorem comm_top (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N : ℤ) :
    augmentation Z T π F N N ≫ targetD F N (N + 1) =
      differential Z T π F N N ≫ augmentation Z T π F N (N + 1) := by
  have hi : N ≤ N := le_refl N
  have hs : tower Z T π F N (depth N N) = step Z T π (initial Z F N) := by
    simp [depth, tower]
  have h : (tower Z T π F N (depth N N)).e ≫
      targetD F (tower Z T π F N (depth N N)).degree (N + 1) = 0 := by
    simpa only [initial, comp_zero] using pair_comm Z T π _ _ hs
  have hz : augmentation Z T π F N (N + 1) = 0 := by
    simp only [augmentation, dif_neg (by omega : ¬ N + 1 ≤ N)]
  rw [hz, comp_zero]
  dsimp only [augmentation]
  rw [dif_pos hi]
  simp only [Category.assoc]
  rw [target_transport F _ (N + 1) N (N + 1) (degree_eq Z T π F N N hi) rfl]
  simpa only [Category.assoc, comp_zero, eqToHom_refl, Category.comp_id] using
    congrArg (fun f ↦ eqToHom (term_eq Z T π F N N hi) ≫ f) h

private theorem tower_laws {A : Type u} [Category.{v} A] [Abelian A]
    (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N : ℤ) :
    ∀ i : ℤ,
      differential Z T π F N i ≫ differential Z T π F N (i + 1) = 0 ∧
      augmentation Z T π F N i ≫ targetD F i (i + 1) =
        differential Z T π F N i ≫ augmentation Z T π F N (i + 1) := by
  intro i
  by_cases hi : i < N
  · exact ⟨square_below Z T π F N i hi, comm_below Z T π F N i hi⟩
  · by_cases h : i = N
    · subst i
      refine ⟨?_, comm_top Z T π F N⟩
      have hz : differential Z T π F N (N + 1) = 0 := by
        simp only [differential, dif_neg (by omega : ¬ N + 1 ≤ N)]
      rw [hz, comp_zero]
    · have hni : ¬ i ≤ N := by omega
      simp [differential, augmentation, hni]

-- Reidentify an assembled degree with the step that constructed it.
private noncomputable def indexedStage (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) : Stage F where
  degree := i
  current := term Z T π F N i
  next := term Z T π F N (i + 1)
  d := differential Z T π F N i
  e := augmentation Z T π F N i

private theorem stage_transport (F : CochainComplex A ℤ) (s : Stage F)
    (i : ℤ) (X Y : A) (hc : X = s.current) (hn : s.next = Y)
    (hg : s.degree = i) :
    (Stage.mk i X Y (eqToHom hc ≫ s.d ≫ eqToHom hn)
      (eqToHom hc ≫ s.e ≫ eqToHom (congrArg (targetTerm F) hg))) = s := by
  cases s
  cases hg
  cases hc
  cases hn
  simp

private theorem stage_d_eq {F : CochainComplex A ℤ} (s t : Stage F) (h : s = t) :
    s.d = eqToHom (congrArg Stage.current h) ≫ t.d ≫
      eqToHom (congrArg Stage.next h).symm := by
  cases h
  simp

private theorem stage_e_eq {F : CochainComplex A ℤ} (s t : Stage F) (h : s = t) :
    s.e = eqToHom (congrArg Stage.current h) ≫ t.e ≫
      eqToHom (congrArg (targetTerm F) (congrArg Stage.degree h).symm) := by
  cases h
  simp

private theorem indexedStage_eq (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    indexedStage Z T π F N i = tower Z T π F N (depth N i) := by
  unfold indexedStage differential augmentation
  simp only [dif_pos hi]
  exact stage_transport F _ i _ _ (term_eq Z T π F N i hi)
    (tower_next Z T π F N i hi) (degree_eq Z T π F N i hi)

private theorem indexedStage_above (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N : ℤ) :
    indexedStage Z T π F N (N + 1) = initial Z F N := by
  have h₁ : ¬ N + 1 ≤ N := by omega
  have h₂ : ¬ N + 1 + 1 ≤ N := by omega
  have hc : term Z T π F N (N + 1) = (initial Z F N).current := by
    simp only [term, if_neg h₁, initial]
  have hn : (initial Z F N).next = term Z T π F N (N + 1 + 1) := by
    simp only [term, if_neg h₂, initial]
  convert stage_transport F (initial Z F N) (N + 1) _ _ hc hn rfl using 1
  simp only [indexedStage, differential, augmentation, dif_neg h₁, initial,
    comp_zero, zero_comp]

private theorem indexedStage_step (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    indexedStage Z T π F N i = step Z T π (indexedStage Z T π F N (i + 1)) := by
  by_cases h : i = N
  · subst i
    rw [indexedStage_above, indexedStage_eq Z T π F N N (le_refl _)]
    simp [depth, tower]
  · have hn : i + 1 ≤ N := by omega
    rw [indexedStage_eq Z T π F N i hi, indexedStage_eq Z T π F N (i + 1) hn]
    have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
    rw [hd, tower]

private noncomputable def indexedPullback (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) : A :=
  pullback (targetD F i (i + 1))
    (kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1))

private theorem term_step_eq (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    term Z T π F N i = T (indexedPullback Z T π F N i) := by
  have hd : i + 1 - 1 = i := by omega
  have h := congrArg Stage.current (indexedStage_step Z T π F N i hi)
  dsimp only [indexedStage, step, stepPullback, cyclesArrow] at h
  have hp := congrArg (fun j : ℤ ↦
    pullback (targetD F j (i + 1))
      (kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1))) hd
  exact h.trans (congrArg (fun G : A ↦ T G) hp)

private theorem pullback_fst_transport (F : CochainComplex A ℤ)
    {Y Z : A} (f : ∀ j : ℤ, targetTerm F j ⟶ Z) (g : Y ⟶ Z)
    {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (fun j ↦ pullback (f j) g) h) ≫ pullback.fst (f k) g =
      pullback.fst (f j) g ≫ eqToHom (congrArg (targetTerm F) h) := by
  cases h
  simp

private theorem pullback_snd_transport (F : CochainComplex A ℤ)
    {Y Z : A} (f : ∀ j : ℤ, targetTerm F j ⟶ Z) (g : Y ⟶ Z)
    {j k : ℤ} (h : j = k) :
    eqToHom (congrArg (fun j ↦ pullback (f j) g) h) ≫ pullback.snd (f k) g =
      pullback.snd (f j) g := by
  cases h
  simp

omit [Abelian A] in
private theorem cover_transport (_Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    {G H : A} (h : G = H) :
    eqToHom (congrArg (fun G : A ↦ T G) h) ≫ π H =
      π G ≫ eqToHom h := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem indexed_augmentation (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    eqToHom (term_step_eq Z T π F N i hi) ≫
      π (indexedPullback Z T π F N i) ≫
      pullback.fst (targetD F i (i + 1))
        (kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1)) =
      augmentation Z T π F N i := by
  have hd : i + 1 - 1 = i := by omega
  let g := kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1)
  let q := fun j : ℤ ↦ pullback (targetD F j (i + 1)) g
  have hs := indexedStage_step Z T π F N i hi
  have hc := congrArg Stage.current hs
  have hp := congrArg q hd
  have he := stage_e_eq _ _ hs
  dsimp only [indexedStage, step] at he
  simp only [Category.assoc] at he
  change augmentation Z T π F N i = eqToHom hc ≫
    π (q (i + 1 - 1)) ≫
    pullback.fst (targetD F (i + 1 - 1) (i + 1)) g ≫
    eqToHom (congrArg (targetTerm F) hd) at he
  change eqToHom (hc.trans (congrArg (fun G : A ↦ T G) hp)) ≫
    π (q i) ≫ pullback.fst (targetD F i (i + 1)) g = _
  rw [← eqToHom_trans hc (congrArg (fun G : A ↦ T G) hp),
    Category.assoc, ← Category.assoc _ _ (pullback.fst _ _), cover_transport Z T π hp]
  simp only [Category.assoc]
  rw [pullback_fst_transport F
    (fun j ↦ targetD F j (i + 1)) g hd]
  exact he.symm

set_option backward.isDefEq.respectTransparency false in
private theorem indexed_differential (Z : A) (T : A → A) (π : ∀ X, T X ⟶ X)
    (F : CochainComplex A ℤ) (N i : ℤ) (hi : i ≤ N) :
    eqToHom (term_step_eq Z T π F N i hi) ≫
      π (indexedPullback Z T π F N i) ≫
      pullback.snd (targetD F i (i + 1))
        (kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1)) ≫
      kernel.ι (differential Z T π F N (i + 1)) = differential Z T π F N i := by
  have hd : i + 1 - 1 = i := by omega
  let g := kernel.ι (differential Z T π F N (i + 1)) ≫ augmentation Z T π F N (i + 1)
  let q := fun j : ℤ ↦ pullback (targetD F j (i + 1)) g
  have hs := indexedStage_step Z T π F N i hi
  have hc := congrArg Stage.current hs
  have hp := congrArg q hd
  have he := stage_d_eq _ _ hs
  dsimp only [indexedStage, step] at he
  simp only [eqToHom_refl, Category.comp_id] at he
  change differential Z T π F N i = eqToHom hc ≫
    π (q (i + 1 - 1)) ≫
    pullback.snd (targetD F (i + 1 - 1) (i + 1)) g ≫
    kernel.ι (differential Z T π F N (i + 1)) at he
  change eqToHom (hc.trans (congrArg (fun G : A ↦ T G) hp)) ≫
    π (q i) ≫ pullback.snd (targetD F i (i + 1)) g ≫
    kernel.ι (differential Z T π F N (i + 1)) = _
  rw [← eqToHom_trans hc (congrArg (fun G : A ↦ T G) hp),
    Category.assoc, ← Category.assoc _ _ (pullback.snd _ _ ≫ _),
    cover_transport Z T π hp]
  simp only [Category.assoc]
  rw [← Category.assoc (eqToHom hp), pullback_snd_transport F
    (fun j ↦ targetD F j (i + 1)) g hd]
  exact he.symm

end SubcategoryResolution

/-- A bounded-above complex admits a termwise epimorphic quasi-isomorphism from a complex
in any quotient-generating class containing a zero object, with the same upper bound.

Source: Stacks Project, Derived Categories, Tag 05T7,
`derived-lemma-subcategory-left-resolution`, part (1)
(blueprint: lem-sfb-subcategory-left-resolution).

Proof (the seven steps of the node):
1. Descend from degree `a + 1`. At stage `n`, prescribe terms in the class in degrees
   at least `n`, zero above `a`, with epic component maps to `K`, an epic map on
   degree-`n` cycles, and cohomology isomorphisms in degrees greater than `n`.
   The chosen zero object in the class supplies the initial stage. Complexes and
   cohomology are those of [def-weil-abstract-derived-category] in [def-sp-abelian].
2. Form `T = K^(n-1) ×_{Z^n K} Z^n P`, using the differential factored through cycles
   and the epic cycle map. Choose an epic cover `Q → T` with `Q` in the class.
   Its projections give the new component and differential. The pullback equation
   gives the chain-map identity, and the cycle inclusion gives the square-zero identity.
3. The new component is epic: lift a generalized element of `K^(n-1)` first along
   the cycle epimorphism and then along `Q → T`, after epimorphic refinements.
   Apply [lem-sp-abelian-refinements](a) and compose the refinements.
4. The new cycle map is epic: a cycle `x` gives the pair `(x, 0)` in `T`. Lift it
   along `Q → T` after an epimorphic refinement. Its zero second component makes
   the lift a cycle. Apply [lem-sp-abelian-refinements](a).
5. The new cohomology map in degree `n` is epic: lift a cohomology class through
   the cycle quotient and then through the epic cycle map, using
   [lem-sp-abelian-refinements](a) twice.
6. It is monic: lift a class in its kernel to a cycle. Its image is a boundary
   after refinement by [lem-sp-abelian-refinements](c). The resulting pair in `T`
   lifts along `Q → T` after another refinement, making the original cycle a boundary.
   Cancel the refinements to get a zero class. Mono and epi imply iso in an abelian
   category, since an epic monomorphism is a cokernel of zero.
7. Recurse on `k : ℕ` with lower endpoint `a + 1 - k`, retaining all assigned data.
   Every integer degree is reached. The cohomology map in degree `j` becomes an
   isomorphism at stage `j - 1` and is unchanged thereafter; above `a` both complexes
   vanish. The resulting chain map is thus a quasi-isomorphism, epic in every degree,
   with all terms in the class and zero terms above `a`.
-/
theorem exists_subcategory_left_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop) (hzero : ∃ Z : C, P Z ∧ IsZero Z)
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.X n)) :
    ∃ (L : CochainComplex C ℤ) (f : L ⟶ K),
      QuasiIso f ∧ (∀ n : ℤ, P (L.X n)) ∧ (∀ n : ℤ, Epi (f.f n)) ∧
        (∀ n : ℤ, a < n → IsZero (L.X n)) := by
  classical
  -- The supplied zero object must be used literally: P need not be iso-closed.
  obtain ⟨Z, hZ, hZ0⟩ := hzero
  choose T π hT hπ using hcover
  let : ∀ X, Epi (π X) := hπ
  let X := SubcategoryResolution.term Z T π K a
  let d := SubcategoryResolution.differential Z T π K a
  let e := SubcategoryResolution.augmentation Z T π K a
  have laws := SubcategoryResolution.tower_laws Z T π K a
  let L : CochainComplex C ℤ := CochainComplex.of X d (fun i ↦ (laws i).1)
  let f : L ⟶ K := CochainComplex.ofHom e (fun i ↦ by
    simpa only [L, CochainComplex.of_d, SubcategoryResolution.targetD] using (laws i).2)
  have hbound (i : ℤ) (hi : a < i) : IsZero (L.X i) := by
    change IsZero (SubcategoryResolution.term Z T π K a i)
    simpa only [SubcategoryResolution.term, if_neg (by omega : ¬ i ≤ a)] using hZ0
  -- Simultaneous lifts of compatible pairs imply both surjectivity and quasi-isomorphy.
  have hlift : ∀ (i : ℤ) (B : C) (x : B ⟶ L.X (i + 1)) (y : B ⟶ K.X i),
      x ≫ L.d (i + 1) (i + 1 + 1) = 0 →
      x ≫ f.f (i + 1) = y ≫ K.d i (i + 1) →
      ∃ (B' : C) (p : B' ⟶ B) (_ : Epi p) (z : B' ⟶ L.X i),
        z ≫ f.f i = p ≫ y ∧ z ≫ L.d i (i + 1) = p ≫ x := by
    intro i B x y hx hy
    by_cases hi : i ≤ a
    · let q := eqToHom (SubcategoryResolution.term_step_eq Z T π K a i hi) ≫
        π (SubcategoryResolution.indexedPullback Z T π K a i)
      have hq₁ : q ≫ pullback.fst _ _ = f.f i := by
        simpa only [q, Category.assoc, f, CochainComplex.ofHom, e] using
          SubcategoryResolution.indexed_augmentation Z T π K a i hi
      have hq₂ : q ≫ pullback.snd _ _ ≫ kernel.ι _ = L.d i (i + 1) := by
        simpa only [q, Category.assoc, L, CochainComplex.of_d, d] using
          SubcategoryResolution.indexed_differential Z T π K a i hi
      have : Epi q := by dsimp only [q]; infer_instance
      have h := cyclePullback_lifting_pointwise f i
      have hdnext : L.d (i + 1) (i + 1 + 1) = d (i + 1) :=
        CochainComplex.of_d X d (i + 1)
      rw [hdnext] at h
      have hx' : x ≫ d (i + 1) = 0 := by
        simpa only [L, CochainComplex.of_d] using hx
      simpa only [L, CochainComplex.of_d] using h q hq₁ hq₂ B x y hx' hy
    · have hy0 : y = 0 := (hK i (by omega)).eq_zero_of_tgt y
      have hx0 : x = 0 := (hbound (i + 1) (by omega)).eq_zero_of_tgt x
      exact ⟨B, 𝟙 B, inferInstance, 0, by simp [hy0], by simp [hx0]⟩
  refine ⟨L, f, ?_, ?_, ?_, hbound⟩
  · rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
    constructor
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
        f (i - 1) i (i + 1) (by simp) (by simp)]
      intro B x hx y hy
      have h := hlift (i - 1)
      rw [show i - 1 + 1 = i by omega] at h
      obtain ⟨B', p, hp, z, _, hz⟩ := h B x y hx hy
      exact ⟨B', p, hp, z, hz.symm⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
        f (i - 1) i (i + 1) (by simp) (by simp)]
      intro B y hy
      obtain ⟨B', p, hp, z, hz, hd⟩ := hlift i B 0 y (by simp) (by simp [hy])
      exact ⟨B', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩
  · intro i
    by_cases hi : i ≤ a
    · change P (SubcategoryResolution.term Z T π K a i)
      simp only [SubcategoryResolution.term, if_pos hi, SubcategoryResolution.depth,
        SubcategoryResolution.tower, SubcategoryResolution.step]
      exact hT _
    · change P (SubcategoryResolution.term Z T π K a i)
      simpa only [SubcategoryResolution.term, if_neg hi] using hZ
  · intro i
    rw [epi_iff_surjective_up_to_refinements]
    intro B y
    obtain ⟨B₁, p₁, hp₁, x₁, hx₁, hd₁⟩ :=
      hlift (i + 1) B 0 (y ≫ K.d i (i + 1)) (by simp) (by simp)
    have hx : x₁ ≫ f.f (i + 1) = (p₁ ≫ y) ≫ K.d i (i + 1) := by
      simpa only [Category.assoc] using hx₁
    obtain ⟨B₂, p₂, hp₂, x₂, hx₂, _⟩ :=
      hlift i B₁ x₁ (p₁ ≫ y) (by simpa using hd₁) hx
    exact ⟨B₂, p₂ ≫ p₁, inferInstance, x₂, by simpa [Category.assoc] using hx₂.symm⟩

end CochainComplex
