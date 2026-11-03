/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Coinduced.SequentialSemilinearSectionProducts

/-! # Epimorphy of the coinduced adjacent difference

Source: Stacks 0941. The finite descending recursion is also used in
`WeilConjectures.CoefficientCoinduction.complexDifference_epi`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived.Coinduced

private theorem descending_lifts (A : ℕ → Type*) [∀ n, AddCommGroup (A n)]
    (t : ∀ n, A (n + 1) → A n) (y : ∀ n, A n) (m : ℕ) (b : A m) :
    ∃ x : ∀ n, A n, x m = b ∧ ∀ n, n < m → t n (x (n + 1)) - x n = y n := by
  induction m with
  | zero =>
    exact ⟨fun n ↦ if h : n = 0 then h.symm ▸ b else 0,
      by simp, fun n h ↦ (Nat.not_lt_zero n h).elim⟩
  | succ m ih =>
    obtain ⟨x, hx, he⟩ := ih (t m b - y m)
    let z : ∀ n, A n := fun n ↦ if h : n = m + 1 then h.symm ▸ b else x n
    refine ⟨z, by simp [z], ?_⟩
    intro n hn
    by_cases hnm : n = m
    · subst n
      simp only [z, dif_pos rfl, dif_neg (by omega : m ≠ m + 1), hx]
      exact sub_sub_cancel _ _
    · have hn' : n < m := by omega
      simpa only [z, dif_neg (by omega : n + 1 ≠ m + 1),
        dif_neg (by omega : n ≠ m + 1)] using he n hn'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

private abbrev cp (K : CochainComplex (StrictRingSystem B) ℤ) :=
  CoinducedSequence.product (complexEvaluation B) (complexRight B) K
private abbrev cd (K : CochainComplex (StrictRingSystem B) ℤ) :=
  CoinducedSequence.difference (complexEvaluation B) (complexRight B)
    (complexAdjunction B) (complexRestriction B) (complexTransition B) K

private def above_sections (n m : ℕ) (hn : n ≤ m)
    (M : systemLevel B n) (U : Cᵒᵖ) :
    (SequenceCoinduced.rightLevel B n M m).val.obj U ≃ M.val.obj U :=
  ((CategoryTheory.forget _).mapIso ((SheafOfModules.evaluation _ U).mapIso
    (SequenceCoinduced.rightAboveIso B n M hn))).toEquiv

private theorem right_section_subsingleton (n m : ℕ) (hn : m < n)
    (M : systemLevel B n) (U : Cᵒᵖ) :
    Subsingleton ((SequenceCoinduced.rightLevel B n M m).val.obj U) := by
  dsimp only [SequenceCoinduced.rightLevel]
  rw [dif_neg (by omega : ¬ n ≤ m)]
  exact ModuleCat.subsingleton_of_isZero
    ((SheafOfModules.evaluation _ U).map_isZero (isZero_zero _))

private theorem transpose_section (n m : ℕ) (hn : n ≤ m)
    (X : StrictRingSystem B) (M : systemLevel B n)
    (f : X.level n ⟶ M) (U : Cᵒᵖ) (x : (X.level m).val.obj U) :
    above_sections B n m hn M U
      ((((SequenceCoinduced.adjunction B n).homEquiv X M f).app m).val.app U x) =
      f.val.app U ((X.transition hn).val.app U x) := by
  dsimp only [SequenceCoinduced.adjunction]
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  change ((SequenceCoinduced.coextendApp B n X M f m) ≫
    (SequenceCoinduced.rightAboveIso B n M hn).hom).val.app U x = _
  rw [SequenceCoinduced.coextendApp_above B n X M f hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem complex_transpose_section (n m : ℕ) (hn : n ≤ m)
    (X : CochainComplex (StrictRingSystem B) ℤ)
    (M : CochainComplex (systemLevel B n) ℤ)
    (f : (complexEvaluation B n).obj X ⟶ M) (q : ℤ)
    (U : Cᵒᵖ) (x : ((X.X q).level m).val.obj U) :
    above_sections B n m hn (M.X q) U
      (((((complexAdjunction B n).homEquiv X M f).f q).app m).val.app U x) =
      (f.f q).val.app U (((X.X q).transition hn).val.app U x) := by
  exact transpose_section B n m hn (X.X q) (M.X q) (f.f q) U x

private def coordinate (K : CochainComplex (StrictRingSystem B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : (((cp B K).X q).level m).val.obj U)
    (n : ℕ) (hn : n ≤ m) : ((K.X q).level n).val.obj U :=
  above_sections B n m hn (((complexEvaluation B n).obj K).X q) U
    ((((Pi.π (fun n ↦ (complexRight B n).obj
      ((complexEvaluation B n).obj K)) n).f q).app m).val.app U x)

private theorem component_section (K : CochainComplex (StrictRingSystem B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : (((cp B K).X q).level m).val.obj U) (n : ℕ) (hn : n ≤ m) :
    ((CoinducedSequence.components (complexEvaluation B) (complexRight B)
      (complexAdjunction B) (𝟙 (cp B K)) n).f q).val.app U
        ((((cp B K).X q).transition hn).val.app U x) =
      coordinate B K q m U x n hn := by
  let p := Pi.π (fun k ↦ (complexRight B k).obj ((complexEvaluation B k).obj K)) n
  dsimp only [CoinducedSequence.components]
  erw [Category.id_comp]
  have h := complex_transpose_section B n m hn (cp B K)
    ((complexEvaluation B n).obj K)
    (((complexAdjunction B n).homEquiv (cp B K)
      ((complexEvaluation B n).obj K)).symm p) q U x
  have hp := congrArg
    (fun g : cp B K ⟶ (complexRight B n).obj ((complexEvaluation B n).obj K) ↦
      above_sections B n m hn (((complexEvaluation B n).obj K).X q) U
        (((g.f q).app m).val.app U x))
    (((complexAdjunction B n).homEquiv (cp B K)
      ((complexEvaluation B n).obj K)).apply_symm_apply p)
  exact h.symm.trans hp

private theorem difference_coordinate (K : CochainComplex (StrictRingSystem B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ)
    (x : (((cp B K).X q).level m).val.obj U) (n : ℕ) (hn : n < m) :
    above_sections B (n + 1) m hn
      (((complexRestriction B n).obj ((complexEvaluation B n).obj K)).X q) U
      ((((Pi.π (fun n ↦ (complexRight B (n + 1)).obj
        ((complexRestriction B n).obj ((complexEvaluation B n).obj K))) n).f q).app m
        ).val.app U ((((cd B K).f q).app m).val.app U x)) =
      (show ((K.X q).level n).val.obj U from
        ((K.X q).transition (Nat.le_succ n)).val.app U
          (coordinate B K q m U x (n + 1) hn)) -
      coordinate B K q m U x n (Nat.le_of_lt hn) := by
  let A := cp B K
  let c := CoinducedSequence.components (complexEvaluation B) (complexRight B)
    (complexAdjunction B) (𝟙 A)
  change above_sections B (n + 1) m hn _ U
    (((((cd B K ≫ Pi.π _ n).f q).app m).val.app U) x) = _
  have hp : cd B K ≫ Pi.π _ n =
      (complexAdjunction B (n + 1)).homEquiv _ _
        ((show (complexEvaluation B (n + 1)).obj A ⟶
            (complexRestriction B n).obj ((complexEvaluation B n).obj K) from
          c (n + 1) ≫ (complexTransition B n).app K) -
          (complexTransition B n).app A ≫ (complexRestriction B n).map (c n)) := by
    dsimp only [cd, CoinducedSequence.difference]
    exact Pi.lift_π _ n
  erw [hp]
  erw [complex_transpose_section]
  change (show ((K.X q).level n).val.obj U from
    ((K.X q).transition (Nat.le_succ n)).val.app U
      (((c (n + 1)).f q).val.app U (((A.X q).transition hn).val.app U x))) -
    (show ((K.X q).level n).val.obj U from ((c n).f q).val.app U
      (((A.X q).transition (Nat.le_succ n)).val.app U
        (((A.X q).transition hn).val.app U x))) = _
  rw [← (A.X q).compose (Nat.le_succ n) hn]
  rw [show ((c (n + 1)).f q).val.app U
      (((A.X q).transition hn).val.app U x) =
        coordinate B K q m U x (n + 1) hn from component_section B K q m U x (n + 1) hn]
  rw [show ((c n).f q).val.app U
      (((A.X q).transition (Nat.le_of_lt hn)).val.app U x) =
        coordinate B K q m U x n (Nat.le_of_lt hn) from
      component_section B K q m U x n (Nat.le_of_lt hn)]

private theorem difference_surjective (K : CochainComplex (StrictRingSystem B) ℤ)
    (q : ℤ) (m : ℕ) (U : Cᵒᵖ) :
    Function.Surjective ((((cd B K).f q).app m).val.app U) := by
  intro y
  let P := fun n ↦ (complexRight B n).obj ((complexEvaluation B n).obj K)
  let Q := fun n ↦ (complexRight B (n + 1)).obj
    ((complexRestriction B n).obj ((complexEvaluation B n).obj K))
  let F := sectionEvaluation B q m U
  let a : ℕ → Type w := fun n ↦ ((K.X q).level n).val.obj U
  let t : ∀ n, a (n + 1) → a n := fun n ↦
    ((K.X q).transition (Nat.le_succ n)).val.app U
  let v : ∀ n, a n := fun n ↦ if hn : n < m then
    above_sections B (n + 1) m hn
      (((complexRestriction B n).obj ((complexEvaluation B n).obj K)).X q) U
        ((((Pi.π Q n).f q).app m).val.app U y) else 0
  obtain ⟨z, _, hz⟩ := descending_lifts a t v m 0
  let w : ∀ n, F.obj (P n) := fun n ↦ if hn : n ≤ m then
    (above_sections B n m hn (((complexEvaluation B n).obj K).X q) U).symm (z n) else
      (0 : (((P n).X q).level m).val.obj U)
  obtain ⟨x, hx⟩ := product_sections B q m U P w
  refine ⟨x, ?_⟩
  apply product_sections_ext B q m U Q
  intro n
  by_cases hn : n < m
  · apply (above_sections B (n + 1) m hn
      (((complexRestriction B n).obj ((complexEvaluation B n).obj K)).X q) U).injective
    change above_sections B (n + 1) m hn _ U
      ((((Pi.π Q n).f q).app m).val.app U
        ((((cd B K).f q).app m).val.app U x)) = _
    erw [difference_coordinate B K q m U x n hn]
    have hc (k : ℕ) (hk : k ≤ m) : coordinate B K q m U x k hk = z k := by
      dsimp only [coordinate]
      change above_sections B k m hk _ U (F.map (Pi.π P k) x) = z k
      rw [hx]
      have hw : w k = (above_sections B k m hk
          (((complexEvaluation B k).obj K).X q) U).symm (z k) := dif_pos hk
      exact (congrArg (above_sections B k m hk
        (((complexEvaluation B k).obj K).X q) U) hw).trans (Equiv.apply_symm_apply _ _)
    rw [hc (n + 1) hn, hc n (Nat.le_of_lt hn)]
    change t n (z (n + 1)) - z n = _
    exact (hz n hn).trans (dif_pos hn)
  · have hs := right_section_subsingleton B (n + 1) m (by omega)
      (((complexRestriction B n).obj ((complexEvaluation B n).obj K)).X q) U
    exact hs.elim _ _

/-- The adjacent difference is an epimorphism of complexes.
Source: Stacks 0941
(blueprint: lem-sf-sequential-semilinear-coinduced-epi).
Proof: in each degree, vertex and section the coinduced products have only finitely
many nonzero coordinates. Given a target tuple, start with zero at the last vertex
and recursively solve transition(x_(n+1)) - x_n = y_n downward. Product preservation
of sections assembles the coordinates. The resulting sectionwise surjectivity detects
epimorphy of strict-system chain maps. Negating the map preserves epimorphy. -/
theorem complexDifference_epi (K : CochainComplex (StrictRingSystem B) ℤ) :
    Epi ((complexDifferenceNat B).app K) := by
  have : Epi (cd B K) := by
    constructor
    intro L a b hab
    apply HomologicalComplex.Hom.ext
    funext q
    apply strictRingSystem_hom_ext B
    intro m
    ext U y
    obtain ⟨x, hx⟩ := difference_surjective B K q m U y
    have hh := congrArg (fun f ↦ (((f.f q).app m).val.app U) x) hab
    change ((a.f q).app m).val.app U ((((cd B K).f q).app m).val.app U x) =
      ((b.f q).app m).val.app U ((((cd B K).f q).app m).val.app U x) at hh
    rw [hx] at hh
    exact hh
  change Epi (-cd B K)
  infer_instance

end SheafOfModules.SequentialDerived.Coinduced
