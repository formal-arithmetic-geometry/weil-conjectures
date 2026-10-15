/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.IndexedCoveringClass
import Mathlib.SetTheory.Cardinal.Regular

/-!
# A small set of covering families representing a covering class

Source: Stacks Project, Sets, Lemma 000X, clauses (1)-(3)
(blueprint: lem-weil-pbc-small-set-of-covering-families).
-/

@[expose] public section

universe u v w

namespace CategoryTheory.PreZeroHypercover

/-- A set of representatives for all target and presieve supports can be selected before
closing it under the covering axioms.  The proof uses separation on the set of targets and
arrow supports, collection of witnessing families, and choice of one witness per support.
This is the first step of the proof of `exists_small_coveringFamilies`.
Source: Stacks Project, Sets, Tag 000X, first paragraph.
(blueprint: lem-weil-pbc-small-set-of-covering-families) -/
private theorem exists_small_covering_representatives {C : Type u} [Category.{v} C]
    (Cov : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    :
    ∃ R : Set (Σ X : C, PreZeroHypercover.{max u v w} X),
      Small.{max u v w} R ∧ R ⊆ Cov ∧
        ∀ (X : C) (E : PreZeroHypercover.{max u v w} X),
          ⟨X, E⟩ ∈ Cov →
            ∃ F : PreZeroHypercover.{max u v w} X,
              ⟨X, F⟩ ∈ R ∧ E.presieve₀ = F.presieve₀ := by
  classical
  let P := {p : (Σ X : C, Presieve X) //
    ∃ E : PreZeroHypercover.{max u v w} p.1, ⟨p.1, E⟩ ∈ Cov ∧ E.presieve₀ = p.2}
  let f : P → (Σ X : C, PreZeroHypercover.{max u v w} X) := fun p ↦
    ⟨p.val.1, Classical.choose p.prop⟩
  have hf (p : P) : f p ∈ Cov ∧ (f p).2.presieve₀ = p.val.2 :=
    Classical.choose_spec p.prop
  have : Small.{max u v w} P := by
    have : Small.{max u v w} (Σ X : C, Presieve X) := small_max _
    exact inferInstance
  refine ⟨Set.range f, inferInstance, ?_, ?_⟩
  · rintro _ ⟨p, rfl⟩
    exact (hf p).1
  · intro X E hE
    let p : P := ⟨⟨X, E.presieve₀⟩, E, hE, rfl⟩
    refine ⟨Classical.choose p.prop, ⟨p, rfl⟩, ?_⟩
    exact (hf p).2.symm

private def coveringStages {A : Type*} (B : Set A) (T : Set A → Set A) :
    Ordinal.{w} → Set A :=
  WellFoundedLT.fix fun α prev ↦ B ∪ ⋃ β : Set.Iio α, T (prev β.val β.prop)

private theorem coveringStages_eq {A : Type*} (B : Set A) (T : Set A → Set A)
    (α : Ordinal.{w}) :
    coveringStages B T α = B ∪ ⋃ β : Set.Iio α, T (coveringStages B T β.val) := by
  exact WellFoundedLT.fix_eq _ α

private theorem coveringStages_small {A : Type*} (B : Set A) (T : Set A → Set A)
    (hB : Small.{w} B) (hT : ∀ (S : Set A), Small.{w} S → Small.{w} (T S))
    (α : Ordinal.{w}) : Small.{w} (coveringStages B T α) := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    rw [coveringStages_eq]
    have : Small.{w} B := hB
    have (β : Set.Iio α) : Small.{w} (T (coveringStages B T β.val)) :=
      hT _ (ih β.val β.prop)
    infer_instance

private theorem coveringStages_bound {A : Type*} (B : Set A) (T : Set A → Set A)
    (P : A → Prop) (hB : ∀ a ∈ B, P a)
    (hT : ∀ S, (∀ a ∈ S, P a) → ∀ a ∈ T S, P a)
    (α : Ordinal.{w}) : ∀ a ∈ coveringStages B T α, P a := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    rw [coveringStages_eq]
    intro a ha
    rcases ha with ha | ha
    · exact hB a ha
    · obtain ⟨β, hβ⟩ := Set.mem_iUnion.mp ha
      exact hT _ (ih β.val β.prop) a hβ

private theorem coveringStages_step {A : Type*} (B : Set A) (T : Set A → Set A)
    {α β : Ordinal.{w}} (h : α < β) :
    T (coveringStages B T α) ⊆ coveringStages B T β := by
  rw [coveringStages_eq B T β]
  intro a ha
  exact Or.inr (Set.mem_iUnion.mpr ⟨⟨α, h⟩, ha⟩)

private theorem coveringStages_mono {A : Type*} (B : Set A) (T : Set A → Set A)
    (hT : ∀ S, S ⊆ T S) : Monotone (coveringStages B T : Ordinal.{w} → Set A) := by
  intro α β h a ha
  rcases h.eq_or_lt with rfl | h
  · exact ha
  · exact coveringStages_step B T h (hT _ ha)

/-- A small subset of a covering class can be closed under the three covering axioms while
remaining small and inside the original class.  The proof is the transfinite construction
from the Stacks sets lemma: choose a cardinal bound, recurse on a sufficiently long ordinal,
and take the union at the limit stage.  This lemma deliberately records only closure; support
representatives are supplied separately by `exists_small_covering_representatives`.
Source: Stacks Project, Sets, Tag 000X, using Tag 05N3.
(blueprint: lem-weil-pbc-small-set-of-covering-families) -/
private theorem exists_small_covering_closure {C : Type u} [Category.{v} C]
    (Cov : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hCov : IsCoveringClass Cov)
    (B : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hsmall : Small.{max u v w} B) (hsub : B ⊆ Cov) :
    ∃ Cov' : Set (Σ X : C, PreZeroHypercover.{max u v w} X),
      Small.{max u v w} Cov' ∧ B ⊆ Cov' ∧ Cov' ⊆ Cov ∧ IsCoveringClass Cov' := by
  classical
  let A := Cov
  choose P p q hp hmem using fun (E : A) (Y : C) (f : Y ⟶ E.val.1) ↦
    hCov.2.2 E.val.1 E.val.2 E.prop Y f
  let pb (E : A) (Y : C) (f : Y ⟶ E.val.1) : A :=
    ⟨⟨Y, { I₀ := E.val.2.I₀, X := P E Y f, f := p E Y f }⟩, hmem E Y f⟩
  let IsoData := Σ X : C, Σ Y : C, { f : Y ⟶ X // IsIso f }
  let iso (d : IsoData) : A :=
    ⟨⟨d.1, singleton d.2.2.val⟩, hCov.1 d.1 d.2.1 d.2.2.val d.2.2.prop⟩
  let B₀ : Set A := { E | E.val ∈ B } ∪ Set.range iso
  have hBsmall : Small.{max u v w} { E : A | E.val ∈ B } := by
    have : Small.{max u v w} B := hsmall
    apply small_of_injective (f := fun E ↦ (⟨E.val.val, E.prop⟩ : B))
    intro E F h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun E : B ↦ E.val) h
  have hIsmall : Small.{max u v w} IsoData := by
    have : Small.{max u v w} C := Small.mk' (Equiv.ulift.{max u v w}).symm
    have (X Y : C) : Small.{max u v w} (X ⟶ Y) :=
      Small.mk' (Equiv.ulift.{max u v w}).symm
    dsimp [IsoData]
    infer_instance
  have hB₀small : Small.{max u v w} B₀ := by
    dsimp [B₀]
    have := hBsmall
    have := hIsmall
    infer_instance
  have : Small.{max u v w} B₀ := hB₀small
  have hbound : BddAbove (Set.range (fun E : B₀ ↦ Cardinal.mk E.val.val.2.I₀)) :=
    Cardinal.bddAbove_of_small
  obtain ⟨κ₀, hκ₀⟩ := hbound
  let κ := max Cardinal.aleph0 κ₀
  have hκ : Cardinal.aleph0 ≤ κ := le_max_left _ _
  have hBκ : ∀ E ∈ B₀, Cardinal.mk E.val.2.I₀ ≤ κ := by
    intro E hE
    exact (hκ₀ ⟨⟨E, hE⟩, rfl⟩).trans (le_max_right _ _)
  let fiber (S : Set A) (X : C) :=
    { E : { E : PreZeroHypercover.{max u v w} X // ⟨X, E⟩ ∈ Cov } //
      (⟨⟨X, E.val⟩, E.prop⟩ : A) ∈ S }
  have hfsmall (S : Set A) (hs : Small.{max u v w} S) (X : C) :
      Small.{max u v w} (fiber S X) := by
    have := hs
    apply small_of_injective (f := fun E : fiber S X ↦
      (⟨⟨⟨X, E.val.val⟩, E.val.prop⟩, E.prop⟩ : S))
    intro E F h
    apply Subtype.ext
    apply Subtype.ext
    have h' := congrArg (fun e : S ↦ e.val.val) h
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h'
  let comp (S : Set A) (E : S) (F : ∀ i : E.val.val.2.I₀, fiber S (E.val.val.2.X i)) : A :=
    ⟨⟨E.val.val.1, E.val.val.2.bind (fun i ↦ (F i).val.val)⟩,
      hCov.2.1 _ _ _ E.val.prop (fun i ↦ (F i).val.prop)⟩
  let CompData (S : Set A) := Σ E : S, ∀ i : E.val.val.2.I₀, fiber S (E.val.val.2.X i)
  let PBData (S : Set A) := Σ E : S, Σ Y : C, Y ⟶ E.val.val.1
  let T (S : Set A) : Set A := S ∪
    Set.range (fun d : CompData S ↦ comp S d.1 d.2) ∪
    Set.range (fun d : PBData S ↦ pb d.1.val d.2.1 d.2.2)
  have hTsmall (S : Set A) (hs : Small.{max u v w} S) : Small.{max u v w} (T S) := by
    have := hs
    have (X : C) := hfsmall S hs X
    have : Small.{max u v w} (CompData S) := by
      dsimp [CompData]
      infer_instance
    have : Small.{max u v w} (PBData S) := by
      have : Small.{max u v w} C := Small.mk' (Equiv.ulift.{max u v w}).symm
      have (X Y : C) : Small.{max u v w} (X ⟶ Y) :=
        Small.mk' (Equiv.ulift.{max u v w}).symm
      dsimp [PBData]
      infer_instance
    dsimp [T]
    infer_instance
  have hTid (S : Set A) : S ⊆ T S := fun _ h ↦ Or.inl (Or.inl h)
  have hTκ (S : Set A) (hs : ∀ E ∈ S, Cardinal.mk E.val.2.I₀ ≤ κ) :
      ∀ E ∈ T S, Cardinal.mk E.val.2.I₀ ≤ κ := by
    intro E hE
    rcases hE with (hE | ⟨d, rfl⟩) | ⟨d, rfl⟩
    · exact hs E hE
    · change Cardinal.mk (Σ i : d.1.val.val.2.I₀, (d.2 i).val.val.I₀) ≤ κ
      calc
        _ = Cardinal.sum (fun i : d.1.val.val.2.I₀ ↦ Cardinal.mk (d.2 i).val.val.I₀) :=
          Cardinal.mk_sigma _
        _ ≤ Cardinal.sum (fun _ : d.1.val.val.2.I₀ ↦ κ) :=
          Cardinal.sum_le_sum _ _ (fun i ↦ hs _ (d.2 i).prop)
        _ = Cardinal.mk d.1.val.val.2.I₀ * κ := Cardinal.sum_const' _ _
        _ ≤ κ * κ := mul_le_mul' (hs _ d.1.prop) le_rfl
        _ = κ := Cardinal.mul_eq_self hκ
    · exact hs d.1.val d.1.prop
  let st : Ordinal.{max u v w} → Set A := coveringStages B₀ T
  have hstsmall (α : Ordinal.{max u v w}) : Small.{max u v w} (st α) :=
    coveringStages_small B₀ T hB₀small hTsmall α
  have hstκ (α : Ordinal.{max u v w}) : ∀ E ∈ st α, Cardinal.mk E.val.2.I₀ ≤ κ :=
    coveringStages_bound B₀ T _ hBκ hTκ α
  have hmono : Monotone st := coveringStages_mono B₀ T hTid
  let θ := (Order.succ κ).ord
  have hreg := Cardinal.isRegular_succ hκ
  have hθ : 0 < θ := hreg.ord_pos
  have hlim : Order.IsSuccLimit θ :=
    Cardinal.isSuccLimit_ord (hκ.trans (Order.le_succ κ))
  have hcof : κ < θ.cof := (Order.lt_succ κ).trans_le hreg.le_cof_ord
  let S : Set A := ⋃ α : Set.Iio θ, st α.val
  have hSsmall : Small.{max u v w} S := by
    have := hstsmall
    dsimp [S]
    infer_instance
  have hSκ : ∀ E ∈ S, Cardinal.mk E.val.2.I₀ ≤ κ := by
    intro E hE
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp hE
    exact hstκ α.val E hα
  have hB₀S : B₀ ⊆ S := by
    intro E hE
    apply Set.mem_iUnion.mpr
    refine ⟨⟨0, hθ⟩, ?_⟩
    change E ∈ coveringStages B₀ T 0
    rw [coveringStages_eq]
    exact Or.inl hE
  have hstepS (α : Set.Iio θ) : T (st α.val) ⊆ S := by
    intro E hE
    exact Set.mem_iUnion.mpr ⟨⟨Order.succ α.val, hlim.succ_lt α.prop⟩,
      coveringStages_step B₀ T (Order.lt_succ α.val) hE⟩
  let Cov' : Set (Σ X : C, PreZeroHypercover.{max u v w} X) := Subtype.val '' S
  have hsmall' : Small.{max u v w} Cov' := by
    have := hSsmall
    dsimp [Cov']
    infer_instance
  have hsub' : Cov' ⊆ Cov := by
    rintro _ ⟨E, _, rfl⟩
    exact E.prop
  have hmemS (E : A) : E.val ∈ Cov' ↔ E ∈ S := by
    constructor
    · rintro ⟨F, hF, hFE⟩
      have : F = E := Subtype.ext hFE
      simpa only [this] using hF
    · intro hE
      exact ⟨E, hE, rfl⟩
  refine ⟨Cov', hsmall', ?_, hsub', ?_, ?_, ?_⟩
  · intro E hE
    exact ⟨⟨E, hsub hE⟩, hB₀S (Or.inl hE), rfl⟩
  · intro X Y f hf
    exact (hmemS (iso ⟨X, Y, f, hf⟩)).mpr (hB₀S (Or.inr ⟨_, rfl⟩))
  · intro X E F hE hF
    let e : A := ⟨⟨X, E⟩, hsub' hE⟩
    let f (i : E.I₀) : A := ⟨⟨E.X i, F i⟩, hsub' (hF i)⟩
    have he : e ∈ S := (hmemS e).mp hE
    have hf (i : E.I₀) : f i ∈ S := (hmemS (f i)).mp (hF i)
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp he
    choose β hβ using fun i : E.I₀ ↦ Set.mem_iUnion.mp (hf i)
    have hsup : (⨆ i, (β i).val) < θ :=
      Ordinal.iSup_lt_of_lt_cof ((hSκ e he).trans_lt hcof) (fun i ↦ (β i).prop)
    let δ := max α.val (⨆ i, (β i).val)
    have hδ : δ < θ := max_lt α.prop hsup
    have heδ : e ∈ st δ := hmono (le_max_left _ _) hα
    have hfδ (i : E.I₀) : f i ∈ st δ :=
      hmono ((Ordinal.le_iSup (fun i ↦ (β i).val) i).trans (le_max_right _ _)) (hβ i)
    let d : CompData (st δ) := ⟨⟨e, heδ⟩,
      fun i ↦ ⟨⟨F i, hsub' (hF i)⟩, hfδ i⟩⟩
    exact (hmemS (comp (st δ) d.1 d.2)).mpr
      (hstepS ⟨δ, hδ⟩ (Or.inl (Or.inr ⟨d, rfl⟩)))
  · intro X E hE Y f
    let e : A := ⟨⟨X, E⟩, hsub' hE⟩
    have he : e ∈ S := (hmemS e).mp hE
    obtain ⟨α, hα⟩ := Set.mem_iUnion.mp he
    refine ⟨P e Y f, p e Y f, q e Y f, hp e Y f, ?_⟩
    exact (hmemS (pb e Y f)).mpr
      (hstepS α (Or.inr ⟨⟨⟨e, hα⟩, Y, f⟩, rfl⟩))

/-- Source: Stacks Project, Sets, Lemma 000X and Section 000W
(blueprint: lem-weil-pbc-small-set-of-covering-families).

Proof plan:
1. The target/support pairs form a small set. Choose one original covering for each
realized pair; retain the target even when the support is empty.
2. Adjoin the prescribed small collection and singleton isomorphisms. Bound all index
cardinalities and the objects and arrows by an infinite cardinal κ. The finite-list
bound `Cardinal.mk_list_le_max` bounds products and dependent sums of these indices.
3. Choose a limit ordinal θ with cofinality greater than κ, using the successor cardinal
of κ and the dependent-sum bound.
4. By `WellFoundedLT.fix`, close the initial collection transfinitely under indexed
composition and one chosen covering pullback presentation for each family and arrow;
at limit stages take unions. Every stage is small, remains in Cov and has indices
bounded by κ.
5. The union at θ contains the prescribed covers and all singleton isomorphisms and
is closed under the chosen covering pullbacks, since θ is a limit.
6. For composition, `Ordinal.iSup_lt_of_lt_cof` bounds the stages of all inner families;
also include the outer family's stage. The composite is added at the next stage.
The initial representatives give equal presieves at the same target, exactly equality
of arrow supports ignoring repetitions. No closure under arbitrary reindexing or under
all possible pullback presentations is asserted. -/
theorem exists_small_coveringFamilies {C : Type u} [Category.{v} C]
    (Cov : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hCov : IsCoveringClass Cov)
    (Cov₀ : Set (Σ X : C, PreZeroHypercover.{max u v w} X))
    (hsmall : Small.{max u v w} Cov₀) (hsub : Cov₀ ⊆ Cov) :
    ∃ Cov' : Set (Σ X : C, PreZeroHypercover.{max u v w} X),
      Small.{max u v w} Cov' ∧ Cov₀ ⊆ Cov' ∧ Cov' ⊆ Cov ∧ IsCoveringClass Cov' ∧
        ∀ (X : C) (E : PreZeroHypercover.{max u v w} X), ⟨X, E⟩ ∈ Cov →
          ∃ F : PreZeroHypercover.{max u v w} X, ⟨X, F⟩ ∈ Cov' ∧ E.presieve₀ = F.presieve₀ := by
  obtain ⟨R, hRsmall, hRsub, hRrep⟩ :=
    exists_small_covering_representatives Cov
  have : Small.{max u v w} Cov₀ := hsmall
  have : Small.{max u v w} R := hRsmall
  have hunion : Small.{max u v w} (Cov₀ ∪ R : Set (Σ X : C,
      PreZeroHypercover.{max u v w} X)) := inferInstance
  obtain ⟨Cov', hCov'small, hsub0, hCov'sub, hCov'ax⟩ :=
    exists_small_covering_closure Cov hCov (Cov₀ ∪ R) hunion (fun x hx ↦
      hx.elim (fun h ↦ hsub h) (fun h ↦ hRsub h))
  refine ⟨Cov', hCov'small, ?_, hCov'sub, hCov'ax, ?_⟩
  · intro x hx
    exact hsub0 (Set.mem_union_left R hx)
  · intro X E hE
    obtain ⟨F, hFR, hEF⟩ := hRrep X E hE
    exact ⟨F, hsub0 (Set.mem_union_right Cov₀ hFR), hEF⟩

end CategoryTheory.PreZeroHypercover
