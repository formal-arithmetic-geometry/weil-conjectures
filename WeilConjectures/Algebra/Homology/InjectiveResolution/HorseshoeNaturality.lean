/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Naturality of the horseshoe construction for injective resolutions

Given a morphism of short exact sequences and "horseshoe" injective resolutions of both, together
with chain maps lifting the outer components, we construct a chain map between the middle
resolutions compatible with everything. The construction is done in three steps, following the
classical proof (Weibel, Theorem 2.4.6; Stacks, Tag 015I):

* `CategoryTheory.InjectiveResolution.horseshoe_degreewise_map`: a degreewise map `t` compatible
  with both outer row squares (but not with the differentials);
* `CategoryTheory.InjectiveResolution.horseshoe_defect_factorization`: the failure of `t` to
  commute with the differentials factors through the outer resolutions, with cocycle identities;
* `CategoryTheory.InjectiveResolution.corrected_middle_map`: subtracting a suitable correction
  yields a chain map compatible with the rows and augmentations.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Degreewise middle map of the horseshoe**: given two rows `X → Y → Z` and `X' → Y' → Z'` of
cochain complexes which are short exact in each degree, with `X` and `X'` degreewise injective,
and chain maps `φA : X ⟶ X'`, `φC : Z ⟶ Z'`, there are maps `t n : Y n ⟶ Y' n` commuting with
both outer squares in each degree (no compatibility with the differentials is claimed).
(blueprint: `lem-weil-pbc-horseshoe-degreewise-map`) -/
theorem horseshoe_degreewise_map {X Y Z X' Y' Z' : CochainComplex C ℕ}
    (α : X ⟶ Y) (β : Y ⟶ Z) (α' : X' ⟶ Y') (β' : Y' ⟶ Z')
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hS : ∀ n, (ShortComplex.mk (α.f n) (β.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f])).ShortExact)
    (hS' : ∀ n, (ShortComplex.mk (α'.f n) (β'.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f])).ShortExact)
    [∀ n, Injective (X.X n)] [∀ n, Injective (X'.X n)]
    (φA : X ⟶ X') (φC : Z ⟶ Z') :
    ∃ t : ∀ n, Y.X n ⟶ Y'.X n, ∀ n,
      α.f n ≫ t n = φA.f n ≫ α'.f n ∧ t n ≫ β'.f n = β.f n ≫ φC.f n := by
  refine ⟨fun n ↦ (hS n).splittingOfInjective.r ≫ φA.f n ≫ α'.f n +
    β.f n ≫ φC.f n ≫ (hS' n).splittingOfInjective.s, fun n ↦ ⟨?_, ?_⟩⟩
  · have h1 := (hS n).splittingOfInjective.f_r
    have h2 : α.f n ≫ β.f n = 0 := by
      rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f]
    dsimp at h1
    rw [Preadditive.comp_add, reassoc_of% h1, reassoc_of% h2, zero_comp, add_zero]
  · have h1 := (hS' n).splittingOfInjective.s_g
    have h2 : α'.f n ≫ β'.f n = 0 := by
      rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f]
    dsimp at h1
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h2, comp_zero, comp_zero,
      zero_add, Category.assoc, Category.assoc, h1, Category.comp_id]

/-- **Correction of the horseshoe middle map**: if `χ : Y ⟶ Y'` commutes with both outer row
squares and `q : Y ⟶ Y'` is killed by `α` and `β'`, and the augmentation defect of `χ` equals
that of `q`, then `χ - q` commutes with both row squares and with the augmentations.
(blueprint: `lem-weil-pbc-horseshoe-correction`) -/
theorem corrected_middle_map {X Y Z X' Y' Z' : CochainComplex C ℕ} {U U' : C}
    (α : X ⟶ Y) (β : Y ⟶ Z) (α' : X' ⟶ Y') (β' : Y' ⟶ Z')
    (φA : X ⟶ X') (φC : Z ⟶ Z') (χ q : Y ⟶ Y')
    (ε : (CochainComplex.single₀ C).obj U ⟶ Y)
    (ε' : (CochainComplex.single₀ C).obj U' ⟶ Y')
    (b : (CochainComplex.single₀ C).obj U ⟶ (CochainComplex.single₀ C).obj U')
    (hχα : α ≫ χ = φA ≫ α') (hχβ : χ ≫ β' = β ≫ φC)
    (hqa : α ≫ q = 0) (hqb : q ≫ β' = 0)
    (hε : ε ≫ χ - ε ≫ q = b ≫ ε') :
    ∃ φB : Y ⟶ Y', ε ≫ φB = b ≫ ε' ∧
      α ≫ φB = φA ≫ α' ∧ φB ≫ β' = β ≫ φC := by
  refine ⟨χ - q, ?_, ?_, ?_⟩
  · simpa only [Preadditive.comp_sub] using hε
  · rw [Preadditive.comp_sub, hχα, hqa, sub_zero]
  · rw [Preadditive.sub_comp, hχβ, hqb, sub_zero]

/-- A map `D` from the middle of a short exact sequence `S₁` to the middle of a short exact
sequence `S₂`, killed by `S₁.f` and by `S₂.g`, factors as `S₁.g ≫ E ≫ S₂.f`. -/
lemma _root_.CategoryTheory.ShortComplex.ShortExact.exists_factor_g_f {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (D : S₁.X₂ ⟶ S₂.X₂) (hD₁ : S₁.f ≫ D = 0)
    (hD₂ : D ≫ S₂.g = 0) : ∃ E : S₁.X₃ ⟶ S₂.X₁, S₁.g ≫ E ≫ S₂.f = D := by
  have := h₁.epi_g
  have := h₂.mono_f
  refine ⟨h₂.exact.lift (h₁.exact.desc D hD₁) ?_, ?_⟩
  · rw [← cancel_epi S₁.g, h₁.exact.g_desc_assoc, hD₂, comp_zero]
  · rw [h₂.exact.lift_f, h₁.exact.g_desc]

/-- Auxiliary version of `horseshoe_defect_factorization` for arbitrary complexes with
augmentations killed by the differentials. -/
theorem horseshoe_defect_factorization_aux {S T : ShortComplex C} (hS : S.ShortExact)
    (F : S ⟶ T) {A B Z A' B' Z' : CochainComplex C ℕ}
    (ιA : S.X₁ ⟶ A.X 0) (ιB : S.X₂ ⟶ B.X 0) (ιC : S.X₃ ⟶ Z.X 0)
    (ιA' : T.X₁ ⟶ A'.X 0) (ιB' : T.X₂ ⟶ B'.X 0) (ιC' : T.X₃ ⟶ Z'.X 0)
    (hιB : ιB ≫ B.d 0 1 = 0) (hιB' : ιB' ≫ B'.d 0 1 = 0)
    (α : A ⟶ B) (β : B ⟶ Z) (α' : A' ⟶ B') (β' : B' ⟶ Z')
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hrow : ∀ n, (ShortComplex.mk (α.f n) (β.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f])).ShortExact)
    (hrow' : ∀ n, (ShortComplex.mk (α'.f n) (β'.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f])).ShortExact)
    (hα : ιA ≫ α.f 0 = S.f ≫ ιB) (hβ : ιB ≫ β.f 0 = S.g ≫ ιC)
    (hα' : ιA' ≫ α'.f 0 = T.f ≫ ιB') (hβ' : ιB' ≫ β'.f 0 = T.g ≫ ιC')
    (φA : A ⟶ A') (φC : Z ⟶ Z')
    (hφA : ιA ≫ φA.f 0 = F.τ₁ ≫ ιA') (hφC : ιC ≫ φC.f 0 = F.τ₃ ≫ ιC')
    (t : ∀ n, B.X n ⟶ B'.X n)
    (htα : ∀ n, α.f n ≫ t n = φA.f n ≫ α'.f n) (htβ : ∀ n, t n ≫ β'.f n = β.f n ≫ φC.f n) :
    ∃ (E : ∀ n, Z.X n ⟶ A'.X (n + 1)) (e : S.X₃ ⟶ A'.X 0),
      (∀ n, β.f n ≫ E n ≫ α'.f (n + 1) = t n ≫ B'.d n (n + 1) - B.d n (n + 1) ≫ t (n + 1)) ∧
      S.g ≫ e ≫ α'.f 0 = ιB ≫ t 0 - F.τ₂ ≫ ιB' ∧
      ιC ≫ E 0 = e ≫ A'.d 0 1 ∧
      ∀ n, Z.d n (n + 1) ≫ E (n + 1) = -(E n ≫ A'.d (n + 1) (n + 1 + 1)) := by
  let D : ∀ n, B.X n ⟶ B'.X (n + 1) := fun n ↦
    t n ≫ B'.d n (n + 1) - B.d n (n + 1) ≫ t (n + 1)
  have hE : ∀ n, ∃ E : Z.X n ⟶ A'.X (n + 1), β.f n ≫ E ≫ α'.f (n + 1) = D n := fun n ↦ by
    refine (hrow n).exists_factor_g_f (hrow' (n + 1)) (D n) ?_ ?_
    · dsimp [D]
      rw [Preadditive.comp_sub, reassoc_of% (htα n), α.comm_assoc, htα, α'.comm,
        φA.comm_assoc, sub_self]
    · dsimp [D]
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, ← β'.comm, reassoc_of% (htβ n),
        htβ, φC.comm, β.comm_assoc, sub_self]
  choose E hE using hE
  have hw : ∃ e : S.X₃ ⟶ A'.X 0, S.g ≫ e ≫ α'.f 0 = ιB ≫ t 0 - F.τ₂ ≫ ιB' := by
    refine hS.exists_factor_g_f (hrow' 0) _ ?_ ?_
    · dsimp
      rw [Preadditive.comp_sub, ← reassoc_of% hα, htα, reassoc_of% hφA, hα', ← F.comm₁₂_assoc,
        sub_self]
    · dsimp
      rw [Preadditive.sub_comp, Category.assoc, Category.assoc, htβ, reassoc_of% hβ, hφC, hβ',
        ← F.comm₂₃_assoc, sub_self]
  obtain ⟨e, he⟩ := hw
  have : ∀ n, Epi (β.f n) := fun n ↦ (hrow n).epi_g
  have : ∀ n, Mono (α'.f n) := fun n ↦ (hrow' n).mono_f
  have : Epi S.g := hS.epi_g
  refine ⟨E, e, hE, he, ?_, fun n ↦ ?_⟩
  · rw [← cancel_epi S.g, ← cancel_mono (α'.f 1)]
    simp only [Category.assoc]
    rw [← α'.comm 0 1, reassoc_of% he, ← reassoc_of% hβ]
    have h0 : β.f 0 ≫ E 0 ≫ α'.f 1 = t 0 ≫ B'.d 0 1 - B.d 0 1 ≫ t 1 := hE 0
    rw [h0]
    simp [Preadditive.comp_sub, Preadditive.sub_comp, reassoc_of% hιB, hιB']
  · rw [← cancel_epi (β.f n), ← cancel_mono (α'.f (n + 1 + 1))]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    rw [β.comm_assoc, hE (n + 1), ← α'.comm (n + 1) (n + 1 + 1), reassoc_of% (hE n)]
    dsimp [D]
    simp [Preadditive.comp_sub, Preadditive.sub_comp]

/-- **Horseshoe defects**: let `F : S ⟶ T` be a morphism of short exact sequences, with
injective resolutions `IA, IB, IC` of the terms of `S` and `JA, JB, JC` of the terms of `T`,
related by chain maps `α, β` and `α', β'` which are short exact in every degree and compatible
with the augmentations. Let `φA`, `φC` be chain maps lifting `F.τ₁`, `F.τ₃`, and let `t` be a
degreewise map commuting with both outer row squares. Then there are maps
`E n : IC n ⟶ JA (n + 1)` and `e : S.X₃ ⟶ JA 0` such that
1. `β ≫ E n ≫ α' = t n ≫ d - d ≫ t (n + 1)`;
2. `S.g ≫ e ≫ α' = ι ≫ t 0 - F.τ₂ ≫ ι`;
3. `ι ≫ E 0 = e ≫ d`;
4. `d ≫ E (n + 1) = - E n ≫ d`.
(blueprint: `lem-weil-pbc-horseshoe-defect-factorization`) -/
theorem horseshoe_defect_factorization {S T : ShortComplex C} (hS : S.ShortExact)
    (F : S ⟶ T)
    {IA : InjectiveResolution S.X₁} {IB : InjectiveResolution S.X₂}
    {IC : InjectiveResolution S.X₃} {JA : InjectiveResolution T.X₁}
    {JB : InjectiveResolution T.X₂} {JC : InjectiveResolution T.X₃}
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hrow : ∀ n, (ShortComplex.mk (α.f n) (β.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ, HomologicalComplex.zero_f])).ShortExact)
    (hrow' : ∀ n, (ShortComplex.mk (α'.f n) (β'.f n)
      (by rw [← HomologicalComplex.comp_f, hαβ', HomologicalComplex.zero_f])).ShortExact)
    (hα : IA.ι.f 0 ≫ α.f 0 = S.f ≫ IB.ι.f 0) (hβ : IB.ι.f 0 ≫ β.f 0 = S.g ≫ IC.ι.f 0)
    (hα' : JA.ι.f 0 ≫ α'.f 0 = T.f ≫ JB.ι.f 0) (hβ' : JB.ι.f 0 ≫ β'.f 0 = T.g ≫ JC.ι.f 0)
    (φA : IA.cocomplex ⟶ JA.cocomplex) (φC : IC.cocomplex ⟶ JC.cocomplex)
    (hφA : IA.ι.f 0 ≫ φA.f 0 = F.τ₁ ≫ JA.ι.f 0) (hφC : IC.ι.f 0 ≫ φC.f 0 = F.τ₃ ≫ JC.ι.f 0)
    (t : ∀ n, IB.cocomplex.X n ⟶ JB.cocomplex.X n)
    (htα : ∀ n, α.f n ≫ t n = φA.f n ≫ α'.f n) (htβ : ∀ n, t n ≫ β'.f n = β.f n ≫ φC.f n) :
    ∃ (E : ∀ n, IC.cocomplex.X n ⟶ JA.cocomplex.X (n + 1)) (e : S.X₃ ⟶ JA.cocomplex.X 0),
      (∀ n, β.f n ≫ E n ≫ α'.f (n + 1) =
        t n ≫ JB.cocomplex.d n (n + 1) - IB.cocomplex.d n (n + 1) ≫ t (n + 1)) ∧
      S.g ≫ e ≫ α'.f 0 = (IB.ι.f 0 ≫ t 0 : S.X₂ ⟶ _) - F.τ₂ ≫ JB.ι.f 0 ∧
      IC.ι.f 0 ≫ E 0 = e ≫ JA.cocomplex.d 0 1 ∧
      ∀ n, IC.cocomplex.d n (n + 1) ≫ E (n + 1) =
        -(E n ≫ JA.cocomplex.d (n + 1) (n + 1 + 1)) :=
  horseshoe_defect_factorization_aux hS F (IA.ι.f 0) (IB.ι.f 0) (IC.ι.f 0) (JA.ι.f 0)
    (JB.ι.f 0) (JC.ι.f 0) IB.ι_f_zero_comp_complex_d JB.ι_f_zero_comp_complex_d α β α' β' hαβ
    hαβ' hrow hrow' hα hβ hα' hβ' φA φC hφA hφC t htα htβ

end CategoryTheory.InjectiveResolution
