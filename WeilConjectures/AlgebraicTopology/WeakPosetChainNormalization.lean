/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.AugmentedPosetChains
public import Mathlib.LinearAlgebra.Quotient.Basic

import Mathlib.Data.List.InsertIdx
import Mathlib.Data.List.Nodup

/-! # Normalization of augmented weak poset chains

Source: Stacks Project, simplicial.tex, Tags 0194 and 0FKI; the explicit augmented
poset adaptation in the DAG (blueprint: lem-sfb-poset-weak-chain-normalization).

Weak lists include all repetitions. Their alternating deletion complex, modulo
the span of repeated lists, is canonically the augmented strict-chain complex.
The comparison also describes the quotient maps induced by monotone maps.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicTopology.WeakPosetChains

/-- Weak lists in integer degree `n`; the unique degree `-1` list is empty.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
def Simplex (P : Type v) [PartialOrder P] (n : ℤ) : Type v :=
  {l : List P // l.Pairwise (· ≤ ·) ∧ (l.length : ℤ) = n + 1}

/-- Free modules on weak lists, with no repetitions killed.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
abbrev chains (R : Type u) [CommRing R] (P : Type v) [PartialOrder P] (n : ℤ) :=
  Simplex P n →₀ R

/-- The weak-list basis vector, or zero if its list has the wrong length or order.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def bracket (R : Type u) [CommRing R] {P : Type v} [PartialOrder P]
    (n : ℤ) (l : List P) : chains R P n :=
  open Classical in
  if h : l.Pairwise (· ≤ ·) ∧ (l.length : ℤ) = n + 1 then
    Finsupp.single ⟨l, h⟩ 1
  else 0

/-- Alternating deletion, including augmentation, and zero off adjacent degrees.
Source: Stacks Tag 0194, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def boundary (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    (i j : ℤ) : ModuleCat.of R (chains R P i) ⟶ ModuleCat.of R (chains R P j) :=
  if i = j + 1 then
    ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P i ↦
      ∑ k ∈ Finset.range c.val.length, (-1 : R) ^ k • bracket R j (c.val.eraseIdx k))
  else 0

/-- The span of repeated weak lists in positive degrees, and zero otherwise.
Source: Stacks Tag 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def repeated (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    (n : ℤ) : Submodule R (chains R P n) :=
  open Classical in
  if 1 ≤ n then
    Submodule.span R {x | ∃ c : Simplex P n, ¬ c.val.Nodup ∧ x = Finsupp.single c 1}
  else ⊥

/-- Kill repeated lists and retain each strict-list generator, including the empty list.
Source: Stacks Tag 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def projection (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    (n : ℤ) : ModuleCat.of R (chains R P n) ⟶
      (AugmentedPosetChains.complex R P).X n :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P n ↦
    AugmentedPosetChains.bracket R n c.val)

/-- Entrywise image of weak lists; in degree `-1` it fixes the empty-list generator.
Source: Stacks Tag 0194, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def mapComponent (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] (f : P →o Q) (n : ℤ) :
    ModuleCat.of R (chains R P n) ⟶ ModuleCat.of R (chains R Q n) :=
  ModuleCat.ofHom (Finsupp.linearCombination R fun c : Simplex P n ↦
    bracket R n (c.val.map f))

private theorem bracket_simplex (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {n : ℤ} (c : Simplex P n) :
    bracket R n c.val = Finsupp.single c 1 := by
  classical
  simp [bracket, c.property]

private theorem map_valid {P Q : Type v} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) {n : ℤ} (c : Simplex P n) :
    (c.val.map f).Pairwise (· ≤ ·) ∧ ((c.val.map f).length : ℤ) = n + 1 := by
  constructor
  · rw [List.pairwise_map]
    exact c.property.1.imp fun h ↦ f.monotone h
  · simpa using c.property.2

private theorem erase_valid {P : Type v} [PartialOrder P] {i j : ℤ}
    (h : i = j + 1) (c : Simplex P i) {k : ℕ} (hk : k < c.val.length) :
    (c.val.eraseIdx k).Pairwise (· ≤ ·) ∧
      ((c.val.eraseIdx k).length : ℤ) = j + 1 := by
  constructor
  · exact c.property.1.sublist (List.eraseIdx_sublist _ _)
  · have hl := c.property.2
    have he := List.length_eraseIdx_of_lt hk
    simp only [he, Nat.cast_sub (by omega : 1 ≤ c.val.length), Nat.cast_one]
    omega

private theorem map_single (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] (f : P →o Q) (n : ℤ)
    (c : Simplex P n) (a : R) :
    mapComponent R f n (Finsupp.single c a) = a • bracket R n (c.val.map f) := by
  simp [mapComponent]

private theorem map_bracket (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] (f : P →o Q) {n : ℤ} (l : List P)
    (hl : l.Pairwise (· ≤ ·) ∧ (l.length : ℤ) = n + 1) :
    mapComponent R f n (bracket R n l) = bracket R n (l.map f) := by
  rw [show bracket R n l = Finsupp.single ⟨l, hl⟩ 1 from bracket_simplex R ⟨l, hl⟩]
  rw [map_single, one_smul]

private theorem boundary_single (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {i j : ℤ} (h : i = j + 1) (c : Simplex P i) (a : R) :
    boundary R P i j (Finsupp.single c a) =
      a • ∑ k ∈ Finset.range c.val.length, (-1 : R) ^ k •
        bracket R j (c.val.eraseIdx k) := by
  simp [boundary, h]

private theorem boundary_bracket (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {i j : ℤ} (h : i = j + 1) (l : List P)
    (hl : l.Pairwise (· ≤ ·) ∧ (l.length : ℤ) = i + 1) :
    boundary R P i j (bracket R i l) =
      ∑ k ∈ Finset.range l.length, (-1 : R) ^ k • bracket R j (l.eraseIdx k) := by
  rw [show bracket R i l = Finsupp.single ⟨l, hl⟩ 1 from bracket_simplex R ⟨l, hl⟩]
  simp [boundary_single R h]

private theorem strict_weak {P : Type v} [PartialOrder P] {n : ℤ}
    (c : AugmentedPosetChains.Simplex P n) :
    c.val.Pairwise (· ≤ ·) ∧ (c.val.length : ℤ) = n + 1 :=
  ⟨c.property.1.imp fun h ↦ h.le, c.property.2⟩

private theorem weak_strict {P : Type v} [PartialOrder P] {n : ℤ}
    (c : Simplex P n) (h : c.val.Nodup) :
    c.val.Pairwise (· < ·) ∧ (c.val.length : ℤ) = n + 1 := by
  exact ⟨(c.property.1.and h).imp (fun h ↦ lt_of_le_of_ne h.1 h.2), c.property.2⟩

private theorem strict_bracket_simplex (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {n : ℤ} (c : AugmentedPosetChains.Simplex P n) :
    AugmentedPosetChains.bracket R n c.val = Finsupp.single c 1 := by
  classical
  simp [AugmentedPosetChains.bracket, c.property]

private theorem projection_single (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] (n : ℤ) (c : Simplex P n) (a : R) :
    projection R P n (Finsupp.single c a) =
      a • AugmentedPosetChains.bracket R n c.val := by
  change (Finsupp.linearCombination R fun c : Simplex P n ↦
    AugmentedPosetChains.bracket R n c.val) (Finsupp.single c a) = _
  exact Finsupp.linearCombination_single _ _ _

private theorem projection_bracket (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {n : ℤ} (l : List P)
    (hl : l.Pairwise (· ≤ ·) ∧ (l.length : ℤ) = n + 1) :
    projection R P n (bracket R n l) = AugmentedPosetChains.bracket R n l := by
  rw [show bracket R n l = Finsupp.single ⟨l, hl⟩ 1 from bracket_simplex R ⟨l, hl⟩]
  rw [projection_single, one_smul]

private noncomputable def sectionMap (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (n : ℤ) : AugmentedPosetChains.chains R P n →ₗ[R] chains R P n :=
  Finsupp.linearCombination R fun c ↦ bracket R n c.val

private theorem projection_section (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (n : ℤ) :
    (projection R P n).hom.comp (sectionMap R P n) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro c a
  change projection R P n (sectionMap R P n (Finsupp.single c a)) = _
  simp only [sectionMap, Finsupp.linearCombination_single, map_smul]
  rw [projection_bracket R _ (strict_weak c), strict_bracket_simplex]
  change a • Finsupp.single c 1 = Finsupp.single c a
  simp

private theorem repeated_single_mem (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {n : ℤ} (c : Simplex P n) (h : ¬c.val.Nodup) :
    Finsupp.single c (1 : R) ∈ repeated R P n := by
  classical
  have hn : 1 ≤ n := by
    have hl := c.property.2
    have he : 2 ≤ c.val.length := by
      have aux : ∀ l : List P, ¬l.Nodup → 2 ≤ l.length := by
        intro l hl
        cases l with
        | nil => simp at hl
        | cons x l =>
          cases l with
          | nil => simp at hl
          | cons y l => simp
      exact aux c.val h
    omega
  rw [repeated, if_pos hn]
  exact Submodule.subset_span ⟨c, h, rfl⟩

private theorem section_projection_mod (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (n : ℤ) :
    ((repeated R P n).mkQ.comp (sectionMap R P n)).comp (projection R P n).hom =
      (repeated R P n).mkQ := by
  classical
  apply Finsupp.lhom_ext
  intro c a
  change (repeated R P n).mkQ
    (sectionMap R P n (projection R P n (Finsupp.single c a))) =
      (repeated R P n).mkQ (Finsupp.single c a)
  rw [projection_single]
  by_cases hn : c.val.Nodup
  · let d : AugmentedPosetChains.Simplex P n := ⟨c.val, weak_strict c hn⟩
    rw [show AugmentedPosetChains.bracket R n c.val = Finsupp.single d 1 from
      strict_bracket_simplex R d]
    simp only [map_smul, sectionMap, Finsupp.linearCombination_single, one_smul]
    rw [show bracket R n d.val = Finsupp.single c 1 from bracket_simplex R c]
    rw [← map_smul]
    congr 1
    simp
  · have hz : AugmentedPosetChains.bracket R n c.val = 0 := by
      apply dif_neg
      exact fun h ↦ hn h.1.nodup
    rw [hz, smul_zero, map_zero, map_zero]
    symm
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    simpa using (repeated R P n).smul_mem a (repeated_single_mem R c hn)

private theorem projection_surjective (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (n : ℤ) : Function.Surjective (projection R P n) := by
  intro y
  exact ⟨sectionMap R P n y, LinearMap.congr_fun (projection_section R P n) y⟩

private theorem strict_bracket_repeated (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] (n : ℤ) (l : List P) (h : ¬l.Nodup) :
    AugmentedPosetChains.bracket R n l = 0 := by
  classical
  apply dif_neg
  exact fun hs ↦ h hs.1.nodup

private theorem projection_kills_repeated (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (n : ℤ) :
    repeated R P n ≤ LinearMap.ker (projection R P n).hom := by
  classical
  by_cases hn : 1 ≤ n
  · rw [repeated, if_pos hn]
    apply Submodule.span_le.mpr
    rintro x ⟨c, hc, rfl⟩
    change projection R P n (Finsupp.single c 1) = 0
    rw [projection_single, one_smul]
    exact strict_bracket_repeated R n c.val hc
  · simp [repeated, hn]

private theorem projection_kernel (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] (n : ℤ) :
    LinearMap.ker (projection R P n).hom = repeated R P n := by
  apply le_antisymm
  · intro x hx
    have h := LinearMap.congr_fun (section_projection_mod R P n) x
    change projection R P n x = 0 at hx
    change (repeated R P n).mkQ (sectionMap R P n (projection R P n x)) =
      (repeated R P n).mkQ x at h
    rw [hx, map_zero, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · exact projection_kills_repeated R P n

private def alternatingFaces (R : Type u) [CommRing R] {P : Type v}
    {M : Type (max u v)} [AddCommGroup M] [Module R M] (l : List P)
    (F : List P → M) : M :=
  ∑ k ∈ Finset.range l.length, (-1 : R) ^ k • F (l.eraseIdx k)

private theorem alternatingFaces_cons (R : Type u) [CommRing R] {P : Type v}
    {M : Type (max u v)} [AddCommGroup M] [Module R M] (a : P) (l : List P)
    (F : List P → M) :
    alternatingFaces R (a :: l) F = F l - alternatingFaces R l (fun t ↦ F (a :: t)) := by
  simp only [alternatingFaces, List.length_cons, Finset.sum_range_succ',
    List.eraseIdx_cons_succ, List.eraseIdx_zero, pow_zero, one_smul,
    pow_succ', mul_smul, neg_one_smul, Finset.sum_neg_distrib]
  abel

private theorem alternatingFaces_sub (R : Type u) [CommRing R] {P : Type v}
    {M : Type (max u v)} [AddCommGroup M] [Module R M] (l : List P)
    (F G : List P → M) :
    alternatingFaces R l (fun t ↦ F t - G t) =
      alternatingFaces R l F - alternatingFaces R l G := by
  simp [alternatingFaces, smul_sub, Finset.sum_sub_distrib]

private theorem alternatingFaces_square (R : Type u) [CommRing R] {P : Type v}
    {M : Type (max u v)} [AddCommGroup M] [Module R M] (l : List P)
    (F : List P → M) :
    alternatingFaces R l (fun t ↦ alternatingFaces R t F) = 0 := by
  induction l generalizing F with
  | nil => simp [alternatingFaces]
  | cons a l ih =>
    rw [alternatingFaces_cons]
    simp_rw [alternatingFaces_cons]
    rw [alternatingFaces_sub, ih]
    simp

private theorem alternatingFaces_adjacent (R : Type u) [CommRing R] {P : Type v}
    {M : Type (max u v)} [AddCommGroup M] [Module R M] (p s : List P) (a : P)
    (F : List P → M) (hF : ∀ l : List P, ¬l.Nodup → F l = 0) :
    alternatingFaces R (p ++ a :: a :: s) F = 0 := by
  induction p generalizing F with
  | nil =>
    simp only [List.nil_append, alternatingFaces_cons]
    have hz : alternatingFaces R s (fun t ↦ F (a :: a :: t)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      change (-1 : R) ^ k • F (a :: a :: s.eraseIdx k) = 0
      rw [hF _ (by simp), smul_zero]
    rw [hz]
    simp
  | cons b p ih =>
    rw [List.cons_append, alternatingFaces_cons, hF, ih]
    · simp
    · intro l hl
      apply hF
      exact fun h ↦ hl (List.nodup_cons.mp h).2
    · simp [List.nodup_append]

private theorem weak_repeated_adjacent {P : Type v} [PartialOrder P] (l : List P)
    (hl : l.Pairwise (· ≤ ·)) (hn : ¬l.Nodup) :
    ∃ p s : List P, ∃ a : P, l = p ++ a :: a :: s := by
  induction l with
  | nil => simp at hn
  | cons a l ih =>
    have hw := List.pairwise_cons.mp hl
    by_cases ht : l.Nodup
    · have ha : a ∈ l := by simpa [List.nodup_cons, ht] using hn
      cases l with
      | nil => simp at ha
      | cons b t =>
        have hab : a = b := by
          rcases List.mem_cons.mp ha with hab | ha
          · exact hab
          · exact le_antisymm (hw.1 b (by simp)) ((List.pairwise_cons.mp hw.2).1 a ha)
        subst b
        exact ⟨[], t, a, rfl⟩
    · obtain ⟨p, s, b, h⟩ := ih hw.2 ht
      exact ⟨a :: p, s, b, by simp [h]⟩

private theorem strict_boundary_weak (R : Type u) [CommRing R] {P : Type v}
    [PartialOrder P] {i j : ℤ} (hij : i = j + 1) (c : Simplex P i) :
    AugmentedPosetChains.boundary R P i j (AugmentedPosetChains.bracket R i c.val) =
      alternatingFaces R c.val (AugmentedPosetChains.bracket R j) := by
  classical
  by_cases hn : c.val.Nodup
  · let d : AugmentedPosetChains.Simplex P i := ⟨c.val, weak_strict c hn⟩
    rw [show AugmentedPosetChains.bracket R i c.val = Finsupp.single d 1 from
      strict_bracket_simplex R d]
    simp [AugmentedPosetChains.boundary, hij, alternatingFaces, d]
  · rw [strict_bracket_repeated R i c.val hn, map_zero]
    obtain ⟨p, s, a, he⟩ := weak_repeated_adjacent c.val c.property.1 hn
    rw [he, alternatingFaces_adjacent R p s a _ (fun l hl ↦ strict_bracket_repeated R j l hl)]

private theorem projection_comm (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (i j : ℤ) :
    projection R P i ≫ (AugmentedPosetChains.complex R P).d i j =
      boundary R P i j ≫ projection R P j := by
  classical
  by_cases h : i = j + 1
  · apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro c a
    change AugmentedPosetChains.boundary R P i j (projection R P i (Finsupp.single c a)) =
      projection R P j (boundary R P i j (Finsupp.single c a))
    rw [projection_single, map_smul, strict_boundary_weak R h c, boundary_single R h,
      map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul, projection_bracket R _ (erase_valid h c (Finset.mem_range.mp hk))]
  · change projection R P i ≫ AugmentedPosetChains.boundary R P i j = _
    simp [AugmentedPosetChains.boundary, boundary, h]

private theorem boundary_square (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] (i j k : ℤ) : boundary R P i j ≫ boundary R P j k = 0 := by
  classical
  by_cases hij : i = j + 1
  · by_cases hjk : j = k + 1
    · apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro c a
      change boundary R P j k (boundary R P i j (Finsupp.single c a)) = 0
      rw [boundary_single R hij, map_smul, map_sum]
      have hz : (∑ t ∈ Finset.range c.val.length, (-1 : R) ^ t •
          boundary R P j k (bracket R j (c.val.eraseIdx t))) = 0 := by
        calc
          _ = alternatingFaces R c.val (fun l ↦
              alternatingFaces R l (bracket R k)) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [boundary_bracket R hjk _ (erase_valid hij c (Finset.mem_range.mp ht))]
            rfl
          _ = 0 := alternatingFaces_square R _ _
      simp only [map_smul]
      rw [hz, smul_zero]
    · simp [boundary, hjk]
  · simp [boundary, hij]

/-- The weak boundary squares to zero and preserves the repeated-list submodules;
the projection is a chain map and kills those submodules.
Source: Stacks Tags 0194 and 0FKI, explicit augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization).

Proof (steps 1--3): deletion preserves weak order. For each pair of original
positions a < b, the two double deletions have equal resulting lists and opposite
coefficients (-1)^(a+b-1) and (-1)^(a+b). This includes the two augmentations
of an edge; at lower degrees one differential is zero. In a repeated weak list,
antisymmetry gives an adjacent equal pair. The two faces removing either member
cancel, and every other face is repeated. For [x,x] the boundary is [x]-[x].
Thus the repeated span is preserved. On strict lists projection commutes with
deletion; on repeated lists the preceding cancellation makes both sides zero.
The empty generator is fixed, and both boundaries out of degree -1 vanish.
Extend all assertions linearly; projection kills the repeated span by definition. -/
theorem boundary_laws (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    [Finite P] :
    (∀ i j : ℤ, ¬ (ComplexShape.down ℤ).Rel i j → boundary R P i j = 0) ∧
    (∀ i j k : ℤ, boundary R P i j ≫ boundary R P j k = 0) ∧
    (∀ i j : ℤ, repeated R P i ≤ (repeated R P j).comap (boundary R P i j).hom) ∧
    (∀ i j : ℤ, projection R P i ≫ (AugmentedPosetChains.complex R P).d i j =
      boundary R P i j ≫ projection R P j) ∧
    (∀ n : ℤ, repeated R P n ≤ LinearMap.ker (projection R P n).hom) := by
  refine ⟨?_, boundary_square R P, ?_, projection_comm R P, projection_kills_repeated R P⟩
  · intro i j h
    have hij : i ≠ j + 1 := by
      intro hij
      apply h
      change j + 1 = i
      exact hij.symm
    simp [boundary, hij]
  · intro i j x hx
    change boundary R P i j x ∈ repeated R P j
    rw [← projection_kernel R P j]
    change projection R P j (boundary R P i j x) = 0
    have h := congrArg (fun t ↦ t x) (projection_comm R P i j)
    change (AugmentedPosetChains.complex R P).d i j (projection R P i x) =
      projection R P j (boundary R P i j x) at h
    have hz := projection_kills_repeated R P i hx
    change projection R P i x = 0 at hz
    rw [hz, map_zero] at h
    exact h.symm

/-- The augmented weak-list chain complex, with actual free modules and deletion maps.
Source: Stacks Tag 0194, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def complex (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    [Finite P] : ChainComplex (ModuleCat.{max u v} R) ℤ where
  X n := ModuleCat.of R (chains R P n)
  d := boundary R P
  shape := (boundary_laws R P).1
  d_comp_d' := fun i j k _ _ ↦ (boundary_laws R P).2.1 i j k

/-- The canonical weak-to-strict chain map.
Source: Stacks Tag 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def comparison (R : Type u) [CommRing R] (P : Type v) [PartialOrder P]
    [Finite P] : complex R P ⟶ AugmentedPosetChains.complex R P where
  f := projection R P
  comm' := fun i j _ ↦ (boundary_laws R P).2.2.2.1 i j

/-- Entrywise image commutes with deletion and preserves repeated lists.
Source: Stacks Tag 0194, explicit augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization).

Proof (step 5): monotonicity preserves weak increase, and entrywise image commutes
with deleting any specified position, with the same sign. In degree zero both
composites send a vertex to the empty generator. Negative differentials are zero.
Equal entries have equal images, so each repeated generator maps into the target
repeated span; in nonpositive degrees the source span is zero. Extend linearly. -/
theorem map_laws (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) :
    (∀ i j : ℤ, mapComponent R f i ≫ boundary R Q i j =
      boundary R P i j ≫ mapComponent R f j) ∧
    (∀ n : ℤ, repeated R P n ≤ (repeated R Q n).comap (mapComponent R f n).hom) := by
  classical
  constructor
  · intro i j
    by_cases h : i = j + 1
    · apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro c a
      change boundary R Q i j (mapComponent R f i (Finsupp.single c a)) =
        mapComponent R f j (boundary R P i j (Finsupp.single c a))
      rw [map_single, map_smul, boundary_bracket R h _ (map_valid f c),
        boundary_single R h, map_smul, map_sum]
      congr 1
      simp only [List.length_map]
      apply Finset.sum_congr rfl
      intro k hk
      rw [map_smul, map_bracket R f _ (erase_valid h c (Finset.mem_range.mp hk))]
      rw [List.eraseIdx_map]
    · simp [boundary, h]
  · intro n
    by_cases h : 1 ≤ n
    · rw [repeated, if_pos h]
      apply Submodule.span_le.mpr
      rintro x ⟨c, hc, rfl⟩
      change mapComponent R f n (Finsupp.single c 1) ∈ repeated R Q n
      rw [map_single, one_smul]
      let d : Simplex Q n := ⟨c.val.map f, map_valid f c⟩
      rw [show bracket R n (c.val.map f) = Finsupp.single d 1 from bracket_simplex R d]
      rw [repeated, if_pos h]
      apply Submodule.subset_span
      refine ⟨d, ?_, rfl⟩
      exact fun hd ↦ hc (List.Nodup.of_map _ hd)
    · simp [repeated, h]

/-- The chain map obtained by entrywise monotone image.
Source: Stacks Tag 0194, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def map (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) :
    complex R P ⟶ complex R Q where
  f := mapComponent R f
  comm' := fun i j _ ↦ (map_laws R f).1 i j

/-- The quotient boundary sends the class of w to the class of its weak boundary.
Source: Stacks Tag 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def quotientBoundary (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] (i j : ℤ) :
    ModuleCat.of R (chains R P i ⧸ repeated R P i) ⟶
      ModuleCat.of R (chains R P j ⧸ repeated R P j) :=
  ModuleCat.ofHom ((repeated R P i).mapQ (repeated R P j) (boundary R P i j).hom
    ((boundary_laws R P).2.2.1 i j))

/-- The quotient differential has the chain-complex shape and squares to zero.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization).

Proof (step 4): every quotient class has a representative w. Off adjacent degrees
its differential is the class of zero. Two successive quotient differentials give
the class of d(d(w)), which is zero by step 1. Well-definedness is the repeated-span
preservation of step 2, already used by quotientBoundary. -/
theorem quotient_boundary_laws (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] :
    (∀ i j : ℤ, ¬ (ComplexShape.down ℤ).Rel i j → quotientBoundary R P i j = 0) ∧
    (∀ i j k : ℤ, quotientBoundary R P i j ≫ quotientBoundary R P j k = 0) := by
  constructor
  · intro i j h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro w
    change (repeated R P j).mkQ ((boundary R P i j) w) = 0
    rw [(boundary_laws R P).1 i j h]
    simp
  · intro i j k
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on _ x ?_
    intro w
    change (repeated R P k).mkQ ((boundary R P j k) ((boundary R P i j) w)) = 0
    have h := congrArg (fun f ↦ f w) ((boundary_laws R P).2.1 i j k)
    change (boundary R P j k) ((boundary R P i j) w) = 0 at h
    rw [h]
    simp

/-- The degreewise quotient by repeated lists, with its induced differential.
Source: Stacks Tag 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def quotientComplex (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] : ChainComplex (ModuleCat.{max u v} R) ℤ where
  X n := ModuleCat.of R (chains R P n ⧸ repeated R P n)
  d := quotientBoundary R P
  shape := (quotient_boundary_laws R P).1
  d_comp_d' := fun i j k _ _ ↦ (quotient_boundary_laws R P).2 i j k

/-- The canonical degreewise quotient map induced by entrywise monotone image.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def quotientMapComponent (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) (n : ℤ) :
    (quotientComplex R P).X n ⟶ (quotientComplex R Q).X n :=
  ModuleCat.ofHom ((repeated R P n).mapQ (repeated R Q n) (mapComponent R f n).hom
    ((map_laws R f).2 n))

/-- The induced quotient maps commute with the quotient differentials.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization).

Proof (step 6): evaluate both composites on the class of w. They are the classes
of d(W(f)(w)) and W(f)(d(w)), equal by step 5. Every class has a representative. -/
theorem quotient_map_comm (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) (i j : ℤ) :
    quotientMapComponent R f i ≫ (quotientComplex R Q).d i j =
      (quotientComplex R P).d i j ≫ quotientMapComponent R f j := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro w
  change (repeated R Q j).mkQ ((boundary R Q i j) ((mapComponent R f i) w)) =
    (repeated R Q j).mkQ ((mapComponent R f j) ((boundary R P i j) w))
  exact congrArg ((repeated R Q j).mkQ) (congrArg (fun t ↦ t w) ((map_laws R f).1 i j))

/-- The chain map on the quotient induced by entrywise monotone image.
Source: Stacks Tags 0194 and 0FKI, augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization). -/
noncomputable def quotientMap (R : Type u) [CommRing R] {P Q : Type v}
    [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q] (f : P →o Q) :
    quotientComplex R P ⟶ quotientComplex R Q where
  f := quotientMapComponent R f
  comm' := fun i j _ ↦ quotient_map_comm R f i j

private noncomputable def quotientLinearEquiv (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] (n : ℤ) :
    (chains R P n ⧸ repeated R P n) ≃ₗ[R] AugmentedPosetChains.chains R P n :=
  LinearEquiv.ofBijective
    ((repeated R P n).liftQ (projection R P n).hom ((boundary_laws R P).2.2.2.2 n))
    (by
      constructor
      · apply LinearMap.ker_eq_bot.mp
        rw [Submodule.ker_liftQ_eq_bot]
        exact (projection_kernel R P n).le
      · intro y
        obtain ⟨x, hx⟩ := projection_surjective R P n y
        exact ⟨(repeated R P n).mkQ x, hx⟩)

private noncomputable def quotientIso (R : Type u) [CommRing R] (P : Type v)
    [PartialOrder P] [Finite P] : quotientComplex R P ≅ AugmentedPosetChains.complex R P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (quotientLinearEquiv R P n).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      refine Submodule.Quotient.induction_on _ x ?_
      intro w
      change (AugmentedPosetChains.complex R P).d i j (projection R P i w) =
        projection R P j (boundary R P i j w)
      exact congrArg (fun t ↦ t w) ((boundary_laws R P).2.2.2.1 i j))

/-- Weak augmented poset chains normalize canonically and naturally to strict chains.
Source: Stacks Tags 0194 and 0FKI; the explicit augmented poset adaptation
(blueprint: lem-sfb-poset-weak-chain-normalization).

Proof (steps 1--6): boundary_laws supplies double-deletion cancellation, the
repeated subcomplex, and the chain-map equation for comparison (steps 1--3).
The weak basis is the disjoint union of strict lists and repeated lists: a weak
list without repetitions is strict by antisymmetry. Uniqueness of a finite basis
expansion shows that the projection kernel is precisely the repeated span.
Every strict basis vector, including the empty one, has the same weak-list
preimage, so comparison is degreewise surjective. Define the quotient comparison
on a class by projecting its representative; its inverse sends each strict basis
vector to the class of that list. Both composites are identities, and step 3
makes them chain maps (step 4). This specifies the isomorphism uniquely, with no
arbitrary choice of its action. Entrywise identity and composition agree on
weak generators and on the empty generator (step 5). On a strict source generator,
the quotient map takes the class of its list to the class of the entrywise image.
The comparison gives its strict bracket: the strict basis vector when the image
is strict, and zero when it has repetitions (step 6). It fixes the empty list.
For empty posets only degree -1 remains; below degree -1 all bases are empty. -/
theorem normalization (R : Type u) [CommRing R] :
    (∀ (P : Type v) [PartialOrder P] [Finite P] (n : ℤ),
      Function.Surjective ((comparison R P).f n) ∧
        LinearMap.ker ((comparison R P).f n).hom = repeated R P n) ∧
    (∀ (P : Type v) [PartialOrder P] [Finite P], map R (OrderHom.id : P →o P) = 𝟙 _) ∧
    (∀ (P Q T : Type v) [PartialOrder P] [PartialOrder Q] [PartialOrder T]
      [Finite P] [Finite Q] [Finite T] (f : P →o Q) (g : Q →o T),
      map R (g.comp f) = map R f ≫ map R g) ∧
    ∃ e : ∀ (P : Type v) [PartialOrder P] [Finite P],
        quotientComplex R P ≅ AugmentedPosetChains.complex R P,
      (∀ (P : Type v) [PartialOrder P] [Finite P] (n : ℤ) (x : chains R P n),
        ((e P).hom.f n) ((repeated R P n).mkQ x) = (comparison R P).f n x) ∧
      (∀ (P Q : Type v) [PartialOrder P] [PartialOrder Q] [Finite P] [Finite Q]
        (f : P →o Q) (n : ℤ) (c : AugmentedPosetChains.Simplex P n),
        ((e Q).hom.f n) ((quotientMap R f).f n
          ((repeated R P n).mkQ (bracket R n c.val))) =
            AugmentedPosetChains.bracket R n (c.val.map f)) := by
  classical
  refine ⟨fun P _ _ n ↦ ⟨projection_surjective R P n, projection_kernel R P n⟩,
    ?_, ?_, ⟨fun P _ _ ↦ quotientIso R P, ?_, ?_⟩⟩
  · intro P _ _
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro c a
    change mapComponent R OrderHom.id n (Finsupp.single c a) = Finsupp.single c a
    rw [map_single]
    simp [bracket_simplex]
  · intro P Q T _ _ _ _ _ _ f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro c a
    change mapComponent R (g.comp f) n (Finsupp.single c a) =
      mapComponent R g n (mapComponent R f n (Finsupp.single c a))
    rw [map_single, map_single, map_smul, map_bracket R g _ (map_valid f c)]
    simp [List.map_map, Function.comp_def]
  · intro P _ _ n x
    rfl
  · intro P Q _ _ _ _ f n c
    change projection R Q n (mapComponent R f n (bracket R n c.val)) = _
    rw [map_bracket R f _ (strict_weak c)]
    exact projection_bracket R _ (map_valid f ⟨c.val, strict_weak c⟩)

end AlgebraicTopology.WeakPosetChains
