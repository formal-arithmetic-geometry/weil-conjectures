/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.Homotopy

/-!
# The forward arithmetic Roos transition and its specified homotopy

Source: Stacks Project, sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok,
and algebra.tex, Tag 00LR, lemma-homotopic-equal-homology. The coordinate calculations
are the ten-step agent proof of (blueprint: lem-weil-roos-transition-homotopy).

We reuse `roosF` and the arithmetic restriction, selection and block constructions.
Index `n : ℕ` denotes positive index `n+1`; its dilate is `e*(n+1)-1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory.RoosTransition

variable {D : Type u} [Category.{v} D] [Abelian D] [HasCountableProducts D]

/-- The product transition T from the arithmetic subsequence to the original tower.
Source: Tag 0941, explicit forward-transition refinement, proof step 1
(blueprint: lem-weil-roos-transition-homotopy). -/
def forward (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) :
    roosP ((complexRestriction D e).obj X) ⟶ roosP X :=
  Pi.lift (fun n ↦ Pi.π
    (fun i : ℕ ↦ ((complexRestriction D e).obj X).asFunctor.obj (op i)) n ≫
      X.asFunctor.map (homOfLE (Nat.le_sub_one_of_lt
        ((Nat.lt_succ_self n).trans_le (Nat.le_mul_of_pos_left (n + 1) he)))).op)

/-- The finite telescoping sum h, including the empty interval when e=1.
Source: Tag 0941, explicit forward-transition refinement, proof steps 4-5
(blueprint: lem-weil-roos-transition-homotopy). -/
def telescope (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) : roosP X ⟶ roosP X :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range (e * (n + 1) - 1 - n),
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (n + k) ≫
      X.asFunctor.map (homOfLE (Nat.le_add_right n k)).op)

/-- The endomorphism phi, with coordinate T_(n,en) x_en.
Source: Tag 0941, explicit forward-transition refinement, proof step 3
(blueprint: lem-weil-roos-transition-homotopy). -/
def phi (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) : roosP X ⟶ roosP X :=
  selection e X.asFunctor ≫ forward X e he

/-- The endomorphism psi, with coordinate sum_(en ≤ i < e(n+1)) T_(n,i) y_i.
Source: Tag 0941, explicit forward-transition refinement, proof step 3
(blueprint: lem-weil-roos-transition-homotopy). -/
def psi (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (e : ℕ) (he : 0 < e) : roosP X ⟶ roosP X :=
  block e X.asFunctor ≫ forward X e he

/-- The complete coordinate, homotopy, localization and naturality assertion.
The witnesses are simultaneous over all strict towers, so the naturality clauses
refer to the same maps and the same explicitly normalized homotopy.
Source: Tag 0941, explicit forward-transition refinement, proof steps 1-10
(blueprint: lem-weil-roos-transition-homotopy). -/
def TransitionHomotopy (D : Type u) [Category.{v} D] [Abelian D]
    [HasCountableProducts D] [HasDerivedCategory.{w} D] : Prop :=
  ∀ (e : ℕ) (he : 0 < e),
    ∃ (res : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        roosF.obj X ⟶ roosF.obj ((complexRestriction D e).obj X))
      (delta : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        roosF.obj ((complexRestriction D e).obj X) ⟶ roosF.obj X)
      (H : ∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        Homotopy (𝟙 (roosF.obj X)) (res X ≫ delta X)),
      (∀ X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ,
        (roosU X ≫ block e X.asFunctor =
          selection e X.asFunctor ≫ roosU ((complexRestriction D e).obj X)) ∧
        (roosU ((complexRestriction D e).obj X) ≫ forward X e he =
          forward X e he ≫ roosU X) ∧
        (∀ p : ℤ,
          (res X).f (p + 1) ≫ (roosχ ((complexRestriction D e).obj X) p).hom =
            (roosχ X p).hom ≫
              biprod.map ((block e X.asFunctor).f p) ((selection e X.asFunctor).f (p + 1))) ∧
        (∀ p : ℤ,
          (delta X).f (p + 1) ≫ (roosχ X p).hom =
            (roosχ ((complexRestriction D e).obj X) p).hom ≫
              biprod.map ((forward X e he).f p) ((forward X e he).f (p + 1))) ∧
        (∀ p : ℤ,
          (res X ≫ delta X).f (p + 1) ≫ (roosχ X p).hom =
            (roosχ X p).hom ≫ biprod.map ((psi X e he).f p) ((phi X e he).f (p + 1))) ∧
        (roosU X ≫ telescope X e = 𝟙 _ - phi X e he) ∧
        (telescope X e ≫ roosU X = 𝟙 _ - psi X e he) ∧
        (∀ p : ℤ,
          (H X).hom (p + 1 + 1) (p + 1) ≫ (roosχ X p).hom =
            (roosχ X (p + 1)).hom ≫
              biprod.lift 0 (-(biprod.fst ≫ (telescope X e).f (p + 1)))) ∧
        QuasiIso (delta X) ∧ QuasiIso (res X) ∧
        (∃ i : DerivedCategory.Q.{w}.obj (roosF.obj X) ≅
            DerivedCategory.Q.{w}.obj (roosF.obj ((complexRestriction D e).obj X)),
          i.hom = DerivedCategory.Q.{w}.map (res X) ∧
          i.inv = DerivedCategory.Q.{w}.map (delta X))) ∧
      (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (a : X ⟶ Y),
        (roosF.map a ≫ res Y = res X ≫ roosF.map ((complexRestriction D e).map a)) ∧
        (roosF.map ((complexRestriction D e).map a) ≫ delta Y = delta X ≫ roosF.map a) ∧
        (roosPmap a ≫ selection e Y.asFunctor = selection e X.asFunctor ≫
          roosPmap ((complexRestriction D e).map a)) ∧
        (roosPmap a ≫ block e Y.asFunctor = block e X.asFunctor ≫
          roosPmap ((complexRestriction D e).map a)) ∧
        (roosPmap ((complexRestriction D e).map a) ≫ forward Y e he =
          forward X e he ≫ roosPmap a) ∧
        (roosPmap a ≫ telescope Y e = telescope X e ≫ roosPmap a) ∧
        (roosPmap a ≫ phi Y e he = phi X e he ≫ roosPmap a) ∧
        (roosPmap a ≫ psi Y e he = psi X e he ≫ roosPmap a) ∧
        (∀ p : ℤ, (H X).hom (p + 1) p ≫ (roosF.map a).f p =
          (roosF.map a).f (p + 1) ≫ (H Y).hom (p + 1) p))

private lemma index_obj (e n : ℕ) : (index e).obj (op n) = op (e * (n + 1) - 1) := rfl

omit [HasCountableProducts D] in
private lemma restricted_asFunctor (e : ℕ) (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    ((complexRestriction D e).obj X).asFunctor = index e ⋙ X.asFunctor := rfl

private lemma index_ge (e : ℕ) (he : 0 < e) (n : ℕ) :
    n ≤ e * (n + 1) - 1 :=
  Nat.le_sub_one_of_lt
    ((Nat.lt_succ_self n).trans_le (Nat.le_mul_of_pos_left (n + 1) he))

private lemma index_next (e : ℕ) (he : 0 < e) (n : ℕ) :
    e * (n + 1 + 1) - 1 = (e * (n + 1) - 1) + e := by
  rw [Nat.mul_succ]
  have : 1 ≤ e * (n + 1) := by nlinarith
  omega

section Products

variable {B : Type*} [Category* B] [Preadditive B]
    (X : ℕᵒᵖ ⥤ B) [HasProduct (fun i : ℕ ↦ X.obj (op i))]

private abbrev proj (n : ℕ) := Pi.π (fun i : ℕ ↦ X.obj (op i)) n

private abbrev trans (n m : ℕ) (h : n ≤ m) := X.map (homOfLE h).op

omit [Preadditive B] [HasProduct (fun i : ℕ ↦ X.obj (op i))] in
private lemma trans_comp (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    trans X b c hbc ≫ trans X a b hab = trans X a c (hab.trans hbc) := by
  rw [← X.map_comp]
  rfl

private def segment (s m : ℕ) : (∏ᶜ fun i : ℕ ↦ X.obj (op i)) ⟶ X.obj (op s) :=
  ∑ k ∈ Finset.range m, proj X (s + k) ≫ trans X s (s + k) (Nat.le_add_right s k)

private lemma segment_zero (s : ℕ) : segment X s 0 = 0 := by simp [segment]

private lemma segment_succ (s m : ℕ) :
    segment X s (m + 1) = segment X s m +
      proj X (s + m) ≫ trans X s (s + m) (Nat.le_add_right s m) := by
  simp only [segment, Finset.sum_range_succ]

omit [Preadditive B] in
private lemma coord_congr (s k l : ℕ) (hk : s ≤ k) (hl : s ≤ l) (h : k = l) :
    proj X k ≫ trans X s k hk = proj X l ≫ trans X s l hl := by
  subst l
  rfl

private lemma segment_split (s a b : ℕ) :
    segment X s (a + b) = segment X s a +
      segment X (s + a) b ≫ trans X s (s + a) (Nat.le_add_right s a) := by
  induction b with
  | zero => simp [segment_zero]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, segment_succ, ih,
      segment_succ, Preadditive.add_comp]
    simp only [Category.assoc, trans_comp]
    simp only [add_assoc]
    congr 2
    exact coord_congr X s _ _ _ _ (Nat.add_assoc s a b).symm

private lemma segment_first (s m : ℕ) :
    segment X s (m + 1) = proj X s +
      segment X (s + 1) m ≫ trans X s (s + 1) (Nat.le_succ s) := by
  simpa [segment, trans, show 1 + m = m + 1 by omega] using segment_split X s 1 m

private lemma telescoping (s m : ℕ) :
    (∑ k ∈ Finset.range m,
      (proj X (s + k) - proj X (s + k + 1) ≫
        trans X (s + k) (s + k + 1) (Nat.le_succ (s + k))) ≫
        trans X s (s + k) (Nat.le_add_right s k)) =
      proj X s - proj X (s + m) ≫
        trans X s (s + m) (Nat.le_add_right s m) := by
  induction m with
  | zero => simp [proj, trans]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Preadditive.sub_comp, Category.assoc, trans_comp]
    rw [coord_congr X s (s + m + 1) (s + (m + 1))
      (by omega) (by omega) (Nat.add_assoc s m 1)]
    abel

end Products

private lemma block_square (e : ℕ) (he : 0 < e)
    (I : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosU I ≫ block e I.asFunctor =
      selection e I.asFunctor ≫ roosU ((complexRestriction D e).obj I) := by
  apply Pi.hom_ext
  intro n
  let s := e * (n + 1) - 1
  have hnext : s + e = e * (n + 1 + 1) - 1 := (index_next e he n).symm
  let X := I.asFunctor
  change (towerTransitionEndomorphism (fun n : ℕ ↦
      X.map (homOfLE (Nat.le_succ n)).op) ≫ block e X) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n =
    (selection e X ≫ towerTransitionEndomorphism (fun n : ℕ ↦
      X.map ((index e).map (homOfLE (Nat.le_succ n)).op))) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n
  simp only [block, selection, towerTransitionEndomorphism,
    towerProductShift, Category.assoc, Pi.lift_π, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_sum, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_π_assoc]
  have ht := telescoping X s e
  simp only [Preadditive.sub_comp, Category.assoc, Finset.sum_sub_distrib] at ht
  dsimp only [s] at ht hnext
  convert ht using 1
  · rfl
  · congr 1
    have hcongr (k l : ℕ) (hk : s ≤ k) (hl : s ≤ l) (hkl : k = l) :
        proj X k ≫ trans X s k hk = proj X l ≫ trans X s l hl := by
      subst l
      rfl
    have h : s ≤ e * (n + 1 + 1) - 1 := by omega
    change proj X (e * (n + 1 + 1) - 1) ≫ trans X s _ h = _
    exact hcongr _ _ _ _ hnext.symm

private lemma forward_square (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosU ((complexRestriction D e).obj X) ≫ forward X e he =
      forward X e he ≫ roosU X := by
  apply Pi.hom_ext
  intro n
  simp only [forward, roosU, towerTransitionEndomorphism, towerProductShift,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    Category.assoc, Pi.lift_π, Pi.lift_π_assoc]
  congr 1
  change _ ≫ X.asFunctor.map ((index e).map (homOfLE (Nat.le_succ n)).op) ≫
      X.asFunctor.map _ = _
  simp only [← Functor.map_comp]
  rfl

private lemma telescope_left (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosU X ≫ telescope X e = 𝟙 _ - phi X e he := by
  apply Pi.hom_ext
  intro n
  simp only [telescope, phi, selection, forward, roosU,
    towerTransitionEndomorphism, towerProductShift, Category.assoc,
    Preadditive.comp_sum, Pi.lift_π, Pi.lift_π_assoc, Preadditive.sub_comp,
    Category.id_comp]
  have ht := telescoping X.asFunctor n (e * (n + 1) - 1 - n)
  have hi : n + (e * (n + 1) - 1 - n) = e * (n + 1) - 1 :=
    Nat.add_sub_of_le (index_ge e he n)
  simp only [Preadditive.sub_comp, Category.assoc, Finset.sum_sub_distrib] at ht
  have hsel : selection e X.asFunctor ≫
      Pi.π (fun i : ℕ ↦ ((complexRestriction D e).obj X).asFunctor.obj (op i)) n =
        proj X.asFunctor (e * (n + 1) - 1) := Pi.lift_π _ _
  dsimp only [selection] at hsel
  rw [← Category.assoc, hsel]
  convert ht using 1
  congr 1
  exact (coord_congr X.asFunctor n _ _ _ _ hi).symm

private lemma telescope_right (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    telescope X e ≫ roosU X = 𝟙 _ - psi X e he := by
  apply Pi.hom_ext
  intro n
  have hn := index_ge e he n
  have hn' := index_ge e he (n + 1)
  have hi : n + (e * (n + 1) - 1 - n) = e * (n + 1) - 1 := Nat.add_sub_of_le hn
  have hlen : e * (n + 1) - 1 - n + e =
      (e * (n + 1 + 1) - 1 - (n + 1)) + 1 := by rw [index_next e he n]; omega
  have hs := segment_split X.asFunctor n (e * (n + 1) - 1 - n) e
  have hf := segment_first X.asFunctor n (e * (n + 1 + 1) - 1 - (n + 1))
  rw [hlen, hf] at hs
  have hseg : segment X.asFunctor (n + (e * (n + 1) - 1 - n)) e ≫
      trans X.asFunctor n _ (Nat.le_add_right n _) =
      segment X.asFunctor (e * (n + 1) - 1) e ≫ trans X.asFunctor n _ hn := by
    have hh (k l : ℕ) (hk : n ≤ k) (hl : n ≤ l) (hkl : k = l) :
        segment X.asFunctor k e ≫ trans X.asFunctor n k hk =
          segment X.asFunctor l e ≫ trans X.asFunctor n l hl := by
      subst l
      rfl
    exact hh _ _ _ _ hi
  rw [hseg] at hs
  simp only [telescope, psi, block, forward, roosU,
    towerTransitionEndomorphism, towerProductShift, Category.assoc,
    Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id,
    Pi.lift_π, Pi.lift_π_assoc]
  have hblock : block e X.asFunctor ≫
      Pi.π (fun i : ℕ ↦ ((complexRestriction D e).obj X).asFunctor.obj (op i)) n =
        segment X.asFunctor (e * (n + 1) - 1) e := Pi.lift_π _ _
  dsimp only [block] at hblock
  rw [← Category.assoc, hblock]
  change segment X.asFunctor n (e * (n + 1) - 1 - n) -
      segment X.asFunctor (n + 1) (e * (n + 1 + 1) - 1 - (n + 1)) ≫
        trans X.asFunctor n (n + 1) (Nat.le_succ n) =
    proj X.asFunctor n - segment X.asFunctor (e * (n + 1) - 1) e ≫
      trans X.asFunctor n _ hn
  exact sub_eq_sub_iff_add_eq_add.mpr hs.symm

omit [HasCountableProducts D] in
private lemma restricted_app (e : ℕ)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) (n : ℕ) :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((complexRestriction D e).map a)).app (op n) =
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app
          ((index e).obj (op n)) := rfl

private lemma selection_natural (e : ℕ)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosPmap a ≫ selection e Y.asFunctor = selection e X.asFunctor ≫
      roosPmap ((complexRestriction D e).map a) := by
  apply Pi.hom_ext
  intro n
  simp [selection, roosPmap, restricted_asFunctor, restricted_app,
    Functor.comp_obj, index_obj, Category.assoc]

private lemma block_natural (e : ℕ)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosPmap a ≫ block e Y.asFunctor = block e X.asFunctor ≫
      roosPmap ((complexRestriction D e).map a) := by
  apply Pi.hom_ext
  intro n
  simp only [block, roosPmap, restricted_asFunctor, restricted_app, Functor.comp_obj,
    index_obj, Category.assoc, Pi.lift_π, Pi.map_π, Pi.map_π_assoc, Preadditive.comp_sum,
    Preadditive.sum_comp, Pi.lift_π_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).naturality _).symm

private lemma forward_natural (e : ℕ) (he : 0 < e)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosPmap ((complexRestriction D e).map a) ≫ forward Y e he =
      forward X e he ≫ roosPmap a := by
  apply Pi.hom_ext
  intro n
  simp only [forward, roosPmap, restricted_asFunctor, restricted_app, Functor.comp_obj,
    index_obj, Category.assoc, Pi.lift_π, Pi.map_π, Pi.map_π_assoc, Pi.lift_π_assoc]
  congr 1
  exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).naturality _).symm

private lemma telescope_natural (e : ℕ)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosPmap a ≫ telescope Y e = telescope X e ≫ roosPmap a := by
  apply Pi.hom_ext
  intro n
  simp only [telescope, roosPmap, Category.assoc, Pi.lift_π, Pi.map_π, Pi.map_π_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp, Pi.lift_π_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  exact ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).naturality _).symm

private lemma forward_selection (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    forward X e he ≫ selection e X.asFunctor =
      phi ((complexRestriction D e).obj X) e he := by
  apply Pi.hom_ext
  intro n
  simp only [phi, selection, forward, restricted_asFunctor, Functor.comp_obj,
    Functor.comp_map, index_obj, Category.assoc, Pi.lift_π, Pi.lift_π_assoc]
  rfl

private lemma forward_block (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    forward X e he ≫ block e X.asFunctor =
      psi ((complexRestriction D e).obj X) e he := by
  apply Pi.hom_ext
  intro n
  simp only [psi, block, forward, restricted_asFunctor, Functor.comp_obj,
    Functor.comp_map, index_obj, Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
    Preadditive.comp_sum, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [← Functor.map_comp]
  rfl

section Cone

omit [HasCountableProducts D]

open CochainComplex CochainComplex.HomComplex

variable {K L M N : CochainComplex D ℤ}

private def coneMap (f : K ⟶ L) (g : M ⟶ N) (a : K ⟶ M) (b : L ⟶ N)
    (h : f ≫ b = a ≫ g) : mappingCocone f ⟶ mappingCocone g :=
  (mappingCone.map f g a b h)⟦(-1 : ℤ)⟧'

private lemma coneMap_χ (f : K ⟶ L) (g : M ⟶ N) (a : K ⟶ M) (b : L ⟶ N)
    (h : f ≫ b = a ≫ g) (p : ℤ) :
    (coneMap f g a b h).f (p + 1) ≫
        ((mappingCone g).shiftFunctorObjXIso (-1) (p + 1) p (by omega) ≪≫
          HomologicalComplex.homotopyCofiber.XIsoBiprod g p (p + 1) rfl ≪≫
          biprod.braiding _ _).hom =
      ((mappingCone f).shiftFunctorObjXIso (-1) (p + 1) p (by omega) ≪≫
          HomologicalComplex.homotopyCofiber.XIsoBiprod f p (p + 1) rfl ≪≫
          biprod.braiding _ _).hom ≫ biprod.map (b.f p) (a.f (p + 1)) := by
  dsimp only [coneMap, Iso.trans_hom]
  rw [CochainComplex.shiftFunctor_map_f']
  simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
  simp only [Category.assoc]
  congr 1
  apply CochainComplex.mappingCone.ext_from f (p + 1) p rfl
  · change (mappingCone.inl f).v (p + 1) p (by omega) ≫
        (mappingCone.map f g a b h).f p ≫ _ = _
    simp only [mappingCone.map, mappingCone.inl_v_desc_f_assoc,
      Cochain.zero_cochain_comp_v]
    simp only [mappingCone.inl, Cochain.mk_v, Category.assoc,
      HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    apply biprod.hom_ext <;> simp
  · rw [mappingCone.map, mappingCone.inr_f_desc_f_assoc]
    simp only [HomologicalComplex.comp_f, mappingCone.inr, Category.assoc]
    apply biprod.hom_ext <;> simp

private lemma coneMap_comp (f : K ⟶ K) (g : L ⟶ L) (h : M ⟶ M)
    (a b : K ⟶ L) (c d : L ⟶ M) (hab : f ≫ b = a ≫ g) (hcd : g ≫ d = c ≫ h) :
    coneMap f g a b hab ≫ coneMap g h c d hcd =
      coneMap f h (a ≫ c) (b ≫ d) (by
        rw [← Category.assoc, hab, Category.assoc, hcd, Category.assoc]) := by
  dsimp only [coneMap]
  rw [← Functor.map_comp, ← mappingCone.map_comp]

private lemma coneMap_fst (f : K ⟶ K) (a b : K ⟶ K) (hab : f ≫ b = a ≫ f) :
    (Cochain.ofHom (mappingCone.map f f a b hab)).comp (mappingCone.fst f).1
        (zero_add 1) =
      (mappingCone.fst f).1.comp (Cochain.ofHom a) (add_zero 1) := by
  ext p q hpq
  subst q
  simp only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rw [mappingCone.map, mappingCone.desc_f f _ _ _ p (p + 1) rfl]
  simp [Category.assoc]

private lemma coneMap_snd (f : K ⟶ K) (a b : K ⟶ K) (hab : f ≫ b = a ≫ f) :
    (Cochain.ofHom (mappingCone.map f f a b hab)).comp (mappingCone.snd f)
        (zero_add 0) =
      (mappingCone.snd f).comp (Cochain.ofHom b) (add_zero 0) := by
  ext p
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rw [mappingCone.map, mappingCone.desc_f f _ _ _ p (p + 1) rfl]
  simp [Category.assoc]

private def coneHomotopy (f h a b : K ⟶ K)
    (hab : f ≫ b = a ≫ f) (ha : f ≫ h = 𝟙 _ - a) (hb : h ≫ f = 𝟙 _ - b) :
    Homotopy (𝟙 (mappingCone f)) (mappingCone.map f f a b hab) :=
  mappingCone.liftHomotopy f _ _
    ((mappingCone.snd f).comp (Cochain.ofHom h) (add_zero 0)) 0
    (by
      rw [coneMap_fst]
      simp only [Cochain.id_comp, δ_comp_ofHom, mappingCone.δ_snd,
        Cochain.neg_comp, neg_neg]
      ext p q hpq
      subst q
      simp [← HomologicalComplex.comp_f,
        ha, HomologicalComplex.sub_f_apply, Preadditive.comp_sub])
    (by
      rw [coneMap_snd]
      ext p
      simp [← HomologicalComplex.comp_f,
        hb, HomologicalComplex.sub_f_apply, Preadditive.comp_sub])

private lemma shifted_hom {P Q : CochainComplex D ℤ} {f g : P ⟶ Q}
    (H : Homotopy f g) (i j i' j' : ℤ) (hi : i' = i + -1) (hj : j' = j + -1) :
    (H.shift (-1)).hom i j =
      -((P.shiftFunctorObjXIso (-1) i i' hi).hom ≫ H.hom i' j' ≫
        (Q.shiftFunctorObjXIso (-1) j j' hj).inv) := by
  subst hi hj
  simp [Homotopy.shift, shiftFunctorObjXIso]

private lemma coneHomotopy_unshifted (f h a b : K ⟶ K)
    (hab : f ≫ b = a ≫ f) (ha : f ≫ h = 𝟙 _ - a) (hb : h ≫ f = 𝟙 _ - b)
    (p : ℤ) :
    (coneHomotopy f h a b hab ha hb).hom (p + 1) p =
      (mappingCone.snd f).v (p + 1) (p + 1) (by omega) ≫ h.f (p + 1) ≫
        (mappingCone.inl f).v (p + 1) p (by omega) := by
  change (if hij : p + 1 + -1 = p then
      (mappingCone.liftCochain f
        ((mappingCone.snd f).comp (Cochain.ofHom h) (add_zero 0)) 0
        (by omega)).v (p + 1) p hij else 0) = _
  rw [dif_pos (by omega)]
  simp only [mappingCone.liftCochain, Cochain.zero_comp, add_zero]
  rw [Cochain.comp_v _ _ _ (p + 1) (p + 1) p (by omega) (by omega)]
  simp

private lemma coneHomotopy_hom (f h a b : K ⟶ K)
    (hab : f ≫ b = a ≫ f) (ha : f ≫ h = 𝟙 _ - a) (hb : h ≫ f = 𝟙 _ - b)
    (p : ℤ) :
    ((coneHomotopy f h a b hab ha hb).shift (-1)).hom (p + 1 + 1) (p + 1) ≫
        ((mappingCone f).shiftFunctorObjXIso (-1) (p + 1) p (by omega) ≪≫
          HomologicalComplex.homotopyCofiber.XIsoBiprod f p (p + 1) rfl ≪≫
          biprod.braiding _ _).hom =
      ((mappingCone f).shiftFunctorObjXIso (-1) (p + 1 + 1) (p + 1) (by omega) ≪≫
          HomologicalComplex.homotopyCofiber.XIsoBiprod f (p + 1) (p + 1 + 1) rfl ≪≫
          biprod.braiding _ _).hom ≫
            biprod.lift 0 (-(biprod.fst ≫ h.f (p + 1))) := by
  rw [shifted_hom _ _ _ (p + 1) p (by omega) (by omega), coneHomotopy_unshifted]
  simp only [Iso.trans_hom, Preadditive.neg_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Preadditive.comp_neg]
  congr 1
  apply mappingCone.ext_from f (p + 1 + 1) (p + 1) rfl
  · apply biprod.hom_ext <;>
      simp [mappingCone.inl, mappingCone.snd, Category.assoc]
  · apply biprod.hom_ext <;>
      simp [mappingCone.inr, mappingCone.inl, mappingCone.snd, Category.assoc]

end Cone

private def resMap (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction D e).obj X) :=
  coneMap (roosU X) (roosU ((complexRestriction D e).obj X))
    (selection e X.asFunctor) (block e X.asFunctor) (block_square e he X)

private def deltaMap (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosF.obj ((complexRestriction D e).obj X) ⟶ roosF.obj X :=
  coneMap (roosU ((complexRestriction D e).obj X)) (roosU X)
    (forward X e he) (forward X e he) (forward_square e he X)

private lemma composite_square (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    roosU X ≫ psi X e he = phi X e he ≫ roosU X := by
  dsimp only [psi, phi]
  rw [← Category.assoc, block_square e he X, Category.assoc,
    forward_square e he X, Category.assoc]

private lemma res_delta_eq (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    resMap e he X ≫ deltaMap e he X =
      coneMap (roosU X) (roosU X) (phi X e he) (psi X e he)
        (composite_square e he X) := coneMap_comp _ _ _ _ _ _ _ _ _

private lemma delta_res_eq (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    deltaMap e he X ≫ resMap e he X =
      coneMap (roosU ((complexRestriction D e).obj X))
        (roosU ((complexRestriction D e).obj X))
        (phi ((complexRestriction D e).obj X) e he)
        (psi ((complexRestriction D e).obj X) e he) (composite_square e he _) := by
  change coneMap _ _ _ _ _ ≫ coneMap _ _ _ _ _ = _
  rw [coneMap_comp]
  congr 1
  · exact forward_selection e he X
  · exact forward_block e he X

private def transitionHomotopy (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    Homotopy (𝟙 (roosF.obj X)) (resMap e he X ≫ deltaMap e he X) where
  hom := ((coneHomotopy (roosU X) (telescope X e) (phi X e he) (psi X e he)
    (composite_square e he X) (telescope_left e he X) (telescope_right e he X)).shift (-1)).hom
  zero := ((coneHomotopy (roosU X) (telescope X e) (phi X e he) (psi X e he)
    (composite_square e he X) (telescope_left e he X) (telescope_right e he X)).shift (-1)).zero
  comm p := by
    have hc := ((coneHomotopy (roosU X) (telescope X e) (phi X e he) (psi X e he)
      (composite_square e he X) (telescope_left e he X)
      (telescope_right e he X)).shift (-1)).comm p
    rw [res_delta_eq]
    simpa only [Functor.map_id, coneMap, roosF, Functor.comp_obj, roosConeFunctor] using hc

private def reverseHomotopy (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) :
    Homotopy (𝟙 (roosF.obj ((complexRestriction D e).obj X)))
      (deltaMap e he X ≫ resMap e he X) := by
  have h := (coneHomotopy (roosU ((complexRestriction D e).obj X))
    (telescope ((complexRestriction D e).obj X) e)
    (phi ((complexRestriction D e).obj X) e he)
    (psi ((complexRestriction D e).obj X) e he)
    (composite_square e he _) (telescope_left e he _) (telescope_right e he _)).shift (-1)
  rw [delta_res_eq]
  simpa only [Functor.map_id, coneMap, roosF, Functor.comp_obj, roosConeFunctor] using h

private lemma transitionHomotopy_χ (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (p : ℤ) :
    (transitionHomotopy e he X).hom (p + 1 + 1) (p + 1) ≫ (roosχ X p).hom =
      (roosχ X (p + 1)).hom ≫
        biprod.lift 0 (-(biprod.fst ≫ (telescope X e).f (p + 1))) := by
  exact coneHomotopy_hom (roosU X) (telescope X e) (phi X e he) (psi X e he)
    (composite_square e he X) (telescope_left e he X) (telescope_right e he X) p


private lemma resMap_χ (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (p : ℤ) :
    (resMap e he X).f (p + 1) ≫ (roosχ ((complexRestriction D e).obj X) p).hom =
      (roosχ X p).hom ≫
        biprod.map ((block e X.asFunctor).f p) ((selection e X.asFunctor).f (p + 1)) :=
  coneMap_χ _ _ _ _ _ p

private lemma deltaMap_χ (e : ℕ) (he : 0 < e)
    (X : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (p : ℤ) :
    (deltaMap e he X).f (p + 1) ≫ (roosχ X p).hom =
      (roosχ ((complexRestriction D e).obj X) p).hom ≫
        biprod.map ((forward X e he).f p) ((forward X e he).f (p + 1)) :=
  coneMap_χ _ _ _ _ _ p

private lemma resMap_natural (e : ℕ) (he : 0 < e)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosF.map a ≫ resMap e he Y =
      resMap e he X ≫ roosF.map ((complexRestriction D e).map a) := by
  change coneMap _ _ (roosPmap a) (roosPmap a) (roosU_natural a) ≫ coneMap _ _ _ _ _ =
    coneMap _ _ _ _ _ ≫ coneMap _ _ (roosPmap ((complexRestriction D e).map a))
      (roosPmap ((complexRestriction D e).map a)) (roosU_natural _)
  rw [coneMap_comp, coneMap_comp]
  congr 1
  · exact selection_natural e a
  · exact block_natural e a

private lemma deltaMap_natural (e : ℕ) (he : 0 < e)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) :
    roosF.map ((complexRestriction D e).map a) ≫ deltaMap e he Y =
      deltaMap e he X ≫ roosF.map a := by
  change coneMap _ _ (roosPmap ((complexRestriction D e).map a))
      (roosPmap ((complexRestriction D e).map a)) (roosU_natural _) ≫ coneMap _ _ _ _ _ =
    coneMap _ _ _ _ _ ≫ coneMap _ _ (roosPmap a) (roosPmap a) (roosU_natural a)
  rw [coneMap_comp, coneMap_comp]
  congr 1 <;> exact forward_natural e he a

private lemma homotopy_natural (e : ℕ) (he : 0 < e)
    {X Y : CochainComplex (ℕᵒᵖ ⥤ D) ℤ} (a : X ⟶ Y) (p : ℤ) :
    (transitionHomotopy e he X).hom (p + 1) p ≫ (roosF.map a).f p =
      (roosF.map a).f (p + 1) ≫ (transitionHomotopy e he Y).hom (p + 1) p := by
  obtain ⟨q, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective p
  change (transitionHomotopy e he X).hom (q + 1 + 1) (q + 1) ≫
      (roosF.map a).f (q + 1) =
    (roosF.map a).f (q + 1 + 1) ≫
      (transitionHomotopy e he Y).hom (q + 1 + 1) (q + 1)
  apply (cancel_mono (roosχ Y q).hom).1
  simp only [Category.assoc]
  rw [roosF_map_χ, ← Category.assoc, transitionHomotopy_χ]
  simp only [Category.assoc]
  rw [transitionHomotopy_χ, reassoc_of% roosF_map_χ a (q + 1)]
  congr 1
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, Preadditive.neg_comp, Preadditive.comp_neg]
    apply neg_injective
    simp only [neg_neg]
    have hm := biprod.map_fst ((roosPmap a).f (q + 1)) ((roosPmap a).f (q + 1 + 1))
    have ht := congrArg (fun f ↦ f.f (q + 1)) (telescope_natural e a)
    change (roosPmap a).f (q + 1) ≫ (telescope Y e).f (q + 1) =
      (telescope X e).f (q + 1) ≫ (roosPmap a).f (q + 1) at ht
    calc
      _ = biprod.fst ≫ (roosPmap a).f (q + 1) ≫
          (telescope Y e).f (q + 1) := by rw [← ht]
      _ = _ := (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ (telescope Y e).f (q + 1)) hm.symm).trans
          (Category.assoc _ _ _))

private theorem transitionHomotopy_all [HasDerivedCategory.{w} D] :
    TransitionHomotopy.{u, v, w} D := by
  intro e he
  refine ⟨resMap e he, deltaMap e he, transitionHomotopy e he, ?_, ?_⟩
  · intro X
    let i : DerivedCategory.Q.{w}.obj (roosF.obj X) ≅
        DerivedCategory.Q.{w}.obj (roosF.obj ((complexRestriction D e).obj X)) :=
      { hom := DerivedCategory.Q.map (resMap e he X)
        inv := DerivedCategory.Q.map (deltaMap e he X)
        hom_inv_id := by
          rw [← Functor.map_comp,
            ← DerivedCategory.Q_map_eq_of_homotopy D (transitionHomotopy e he X),
            Functor.map_id]
        inv_hom_id := by
          rw [← Functor.map_comp,
            ← DerivedCategory.Q_map_eq_of_homotopy D (reverseHomotopy e he X),
            Functor.map_id] }
    have hi : IsIso (DerivedCategory.Q.{w}.map (resMap e he X)) := i.isIso_hom
    have hj : IsIso (DerivedCategory.Q.{w}.map (deltaMap e he X)) := i.isIso_inv
    refine ⟨block_square e he X, forward_square e he X, resMap_χ e he X,
      deltaMap_χ e he X, ?_, telescope_left e he X, telescope_right e he X,
      transitionHomotopy_χ e he X,
      (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mp hj,
      (DerivedCategory.isIso_Q_map_iff_quasiIso D _).mp hi, i, rfl, rfl⟩
    intro p
    simp only [HomologicalComplex.comp_f, Category.assoc, deltaMap_χ]
    rw [← Category.assoc, resMap_χ, Category.assoc]
    congr 1
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, psi, HomologicalComplex.comp_f]
      change biprod.map ((block e X.asFunctor).f p)
          ((selection e X.asFunctor).f (p + 1)) ≫ biprod.fst ≫ (forward X e he).f p =
        biprod.fst ≫ (block e X.asFunctor).f p ≫ (forward X e he).f p
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ (forward X e he).f p)
          (biprod.map_fst _ _)).trans (Category.assoc _ _ _))
    · simp only [Category.assoc, biprod.map_snd, phi, HomologicalComplex.comp_f]
      change biprod.map ((block e X.asFunctor).f p)
          ((selection e X.asFunctor).f (p + 1)) ≫ biprod.snd ≫
            (forward X e he).f (p + 1) =
        biprod.snd ≫ (selection e X.asFunctor).f (p + 1) ≫ (forward X e he).f (p + 1)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f ↦ f ≫ (forward X e he).f (p + 1))
          (biprod.map_snd _ _)).trans (Category.assoc _ _ _))
  · intro X Y a
    refine ⟨resMap_natural e he a, deltaMap_natural e he a, selection_natural e a,
      block_natural e a, forward_natural e he a, telescope_natural e a, ?_, ?_,
      homotopy_natural e he a⟩
    · dsimp only [phi]
      rw [← Category.assoc, selection_natural, Category.assoc, forward_natural, Category.assoc]
    · dsimp only [psi]
      rw [← Category.assoc, block_natural, Category.assoc, forward_natural, Category.assoc]

/-- The forward Roos transition is the inverse of the finite-block restriction, with
exactly the displayed telescoping homotopy. This holds for constant A-coefficients
and for every sheaf of commutative A-algebras, with all arrows and homotopies linear
in that module category. The algebra clause imposes no exact-product hypothesis.

Source: sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok, Roos model;
algebra.tex, Tag 00LR, lemma-homotopic-equal-homology. Explicit agent refinement
(blueprint: lem-weil-roos-transition-homotopy).

Proof, following the node's ten steps:
1. Product projections and composites of transitions define all maps. The tower law
   gives fT=Tf_e, hence the diagonal forward map is a chain map.
2. The block sum telescopes to b_e f=f_e a_e, giving the restriction chain map.
3. The two composite coordinates are T b_e=psi and T a_e=phi.
4. Telescoping [n,en) gives hf=1-phi, also for the empty interval e=1.
5. Subtracting [n,en) and [n+1,e(n+1)) gives fh=1-psi.
6. Since dh=hd, H(y,x)=(0,-hy) gives dH+Hd=(fhy,hfx)=1-delta res,
   with the stated shifted-cone signs (def-weil-abstract-derived-category).
7. For the subsequence tower L_n=K_en, the other composite has the same phi/psi
   formulas for L. Repeating the finite-sum calculation gives the opposite homotopy.
8. A null-homotopy induces zero on ker(d)/im(d), so the two maps induce inverse
   cohomology isomorphisms (Tag 00LR).
9. Localization through the homotopy category gives the specified inverse equality.
10. A strict tower morphism commutes with every composite transition, proving all
    naturality identities. Products of R-modules are sectionwise products with
    coordinatewise action and gluing; projections, sums and transitions are linear.
    Steps 1-9 apply there without needing products to be exact. -/
theorem roos_transition_homotopy
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J RingCat.{max uC vC r}]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A : Type (max uC vC r)) [CommRing A]
    [HasDerivedCategory.{w}
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A)))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A)))] :
    TransitionHomotopy.{_, _, w}
      (ringedSiteModules.{max uC vC r} ((constantSheaf J RingCat).obj (RingCat.of A))) ∧
    ∀ (R : Sheaf J RingCat.{max uC vC r})
      (_algebra : (constantSheaf J RingCat).obj (RingCat.of A) ⟶ R)
      (_comm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
      [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)],
      TransitionHomotopy.{_, _, w} (ringedSiteModules.{max uC vC r} R) := by
  refine ⟨transitionHomotopy_all, ?_⟩
  intro R _algebra _comm _
  exact transitionHomotopy_all

end CategoryTheory.RoosTransition
