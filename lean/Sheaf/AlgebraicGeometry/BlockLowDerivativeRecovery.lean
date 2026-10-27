/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.List.Perm.Basic

/-!
# Recovery of low derivatives by degree-block induction

Source: Bierstone--Milman, Invent. Math. 128 (1997), Remark 7.16, Lemma 7.17,
and the induction in Theorem 7.14, pp.267--268; ILO VIII 2.3.11--2.3.13
for the route (blueprint: lem-trf-block-low-derivative-recovery).

Blocks are indexed by the distinct degrees that occur, rather than by their positions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.HilbertCoefficient

private theorem coordinate_span {L : Type u} [Field L] {m n s b : ℕ}
    (a : Fin s → Fin n →₀ ℕ) :
    transverseIdeal (m := m) (R := L) a b =
      Ideal.span (Set.range (fun j : {j : Fin n // essential a b j} ↦
        (MvPowerSeries.X (Sum.inr j.val) : MvPowerSeries (Fin m ⊕ Fin n) L))) := by
  unfold transverseIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.property, rfl⟩

open Classical in
private theorem coordinate_jacobian_span {L : Type u} [Field L] {m n s b : ℕ}
    (a : Fin s → Fin n →₀ ℕ)
    (g : {j : Fin n // essential a b j} → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hg : ∀ j, g j ∈ transverseIdeal a b)
    (hdet : Matrix.det (fun j l : {j : Fin n // essential a b j} ↦
      MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (Sum.inr l.val) (g j))) ≠ 0) :
    Ideal.span (Set.range g) = transverseIdeal a b := by
  classical
  let x : {j : Fin n // essential a b j} → MvPowerSeries (Fin m ⊕ Fin n) L :=
    fun j ↦ MvPowerSeries.X (Sum.inr j.val)
  have hrep : ∀ j, ∃ c : {j : Fin n // essential a b j} →
      MvPowerSeries (Fin m ⊕ Fin n) L, ∑ l, c l * x l = g j := by
    intro j
    exact Ideal.mem_span_range_iff_exists_fun.mp ((coordinate_span (L := L) (m := m) a).symm ▸ hg j)
  choose c hc using hrep
  let C : Matrix {j : Fin n // essential a b j} {j : Fin n // essential a b j}
      (MvPowerSeries (Fin m ⊕ Fin n) L) := c
  have hC : C.mulVec x = g := funext hc
  have hcoeff : ∀ j l, MvPowerSeries.constantCoeff (C j l) =
      MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (Sum.inr l.val) (g j)) := by
    intro j l
    rw [← hc j]
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
    simp [x, C, MvPowerSeries.pderiv_X, Pi.single_apply, Subtype.val_inj]
  have hunit : IsUnit C.det := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [(MvPowerSeries.constantCoeff : MvPowerSeries (Fin m ⊕ Fin n) L →+* L).map_det]
    have heq :
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin m ⊕ Fin n) L →+* L).mapMatrix C =
        (fun j l ↦ MvPowerSeries.constantCoeff
          (MvPowerSeries.pderiv L (Sum.inr l.val) (g j))) := by
      ext j l
      exact hcoeff j l
    rw [heq]
    exact isUnit_iff_ne_zero.mpr hdet
  have hback : C⁻¹.mulVec g = x := by
    rw [← hC, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul C hunit,
      Matrix.one_mulVec]
  apply le_antisymm
  · exact Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hg j)
  · rw [coordinate_span a]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change x j ∈ Ideal.span (Set.range g)
    rw [← hback]
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun l ↦ C⁻¹ j l, rfl⟩

private theorem partial_commute {σ : Type*} {R : Type u} [CommRing R]
    (i j : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.pderiv R i (MvPowerSeries.pderiv R j f) =
      MvPowerSeries.pderiv R j (MvPowerSeries.pderiv R i f) := by
  classical
  ext d
  simp only [MvPowerSeries.coeff_pderiv]
  by_cases h : i = j
  · subst j
    rfl
  · simp only [Finsupp.add_apply, Finsupp.single_eq_of_ne h,
      Finsupp.single_eq_of_ne (Ne.symm h), add_zero]
    rw [add_right_comm d, mul_right_comm]

private theorem partial_add {σ : Type*} {R : Type u} [CommRing R] [Fintype σ]
    (α β : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    iteratedPartial (α + β) f = iteratedPartial β (iteratedPartial α f) := by
  classical
  unfold iteratedPartial
  have hperm : (Finset.univ.toList.flatMap fun j : σ ↦
      List.replicate ((α + β) j) j).Perm
      ((Finset.univ.toList.flatMap fun j : σ ↦ List.replicate (α j) j) ++
        (Finset.univ.toList.flatMap fun j : σ ↦ List.replicate (β j) j)) := by
    apply List.perm_iff_count.mpr
    intro j
    simp [List.count_flatMap, List.count_replicate, Finset.sum_ite_eq']
  rw [hperm.foldl_eq' (fun i _ j _ g ↦ partial_commute j i g), List.foldl_append]

private theorem fullVertex_inl {m n : ℕ} (α : Fin n →₀ ℕ) (i : Fin m) :
    fullVertex m α (Sum.inl i) = 0 := by
  exact Finsupp.mapDomain_of_notMem_range _ _ (by simp)

private theorem fullVertex_inr {m n : ℕ} (α : Fin n →₀ ℕ) (j : Fin n) :
    fullVertex m α (Sum.inr j) = α j :=
  Finsupp.mapDomain_apply Sum.inr_injective α j

private theorem partial_coordinate_mem {R : Type u} [CommRing R] {m n s b : ℕ}
    (a : Fin s → Fin n →₀ ℕ) (x : Fin m ⊕ Fin n)
    (hx : ∀ j, essential a b j → x ≠ Sum.inr j)
    {g : MvPowerSeries (Fin m ⊕ Fin n) R} (hg : g ∈ transverseIdeal a b) :
    MvPowerSeries.pderiv R x g ∈ transverseIdeal a b := by
  classical
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := hg
    simp [MvPowerSeries.pderiv_X_of_ne (hx j hj).symm]
  | zero => simp
  | add g h hg hh ig ih =>
    simpa only [map_add] using (transverseIdeal a b).add_mem ig ih
  | smul r g hg ih =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact (transverseIdeal a b).add_mem
      ((transverseIdeal a b).mul_mem_left r ih)
      ((transverseIdeal a b).mul_mem_right _ hg)

private theorem partial_complement_mem {R : Type u} [CommRing R] {m n s b : ℕ}
    (a : Fin s → Fin n →₀ ℕ) (ρ : (Fin m ⊕ Fin n) →₀ ℕ)
    (hρ : ∀ j, essential a b j → ρ (Sum.inr j) = 0)
    {g : MvPowerSeries (Fin m ⊕ Fin n) R} (hg : g ∈ transverseIdeal a b) :
    iteratedPartial ρ g ∈ transverseIdeal a b := by
  classical
  have hfold : ∀ (l : List (Fin m ⊕ Fin n)),
      (∀ x ∈ l, ρ x ≠ 0) → ∀ g ∈ transverseIdeal (R := R) (m := m) a b,
      l.foldl (fun h x ↦ MvPowerSeries.pderiv R x h) g ∈ transverseIdeal a b := by
    intro l
    induction l with
    | nil => intro _ g hg; exact hg
    | cons x l ih =>
      intro hl g hg
      apply ih (fun y hy ↦ hl y (by simp [hy]))
      apply partial_coordinate_mem a x ?_ hg
      intro j hj heq
      exact hl x (by simp) (heq ▸ hρ j hj)
  apply hfold _ ?_ g hg
  intro x hx
  obtain ⟨j, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨hj, rfl⟩ := List.mem_replicate.mp hx
  exact hj

private theorem partial_diagram_mem {R : Type u} [CommRing R] {m n s b Q : ℕ}
    (a : Fin s → Fin n →₀ ℕ) (f : MvPowerSeries (Fin m ⊕ Fin n) R)
    (hsupported : ∀ δ : Fin n →₀ ℕ, δ.degree ≤ Q →
      (∀ j, δ j ≠ 0 → essential a b j) → inDiagram a b δ →
      iteratedPartial (fullVertex m δ) f ∈ transverseIdeal a b)
    (γ : (Fin m ⊕ Fin n) →₀ ℕ) (hγ : γ.degree ≤ Q)
    (hdiagram : ∃ j : Fin s, (a j).degree ≤ b ∧ fullVertex m (a j) ≤ γ) :
    iteratedPartial γ f ∈ transverseIdeal a b := by
  classical
  let δ : Fin n →₀ ℕ :=
    (Finsupp.comapDomain.addMonoidHom Sum.inr_injective γ).filter (essential a b)
  have hδ (j : Fin n) : δ j = if essential a b j then γ (Sum.inr j) else 0 := by
    simp [δ, Finsupp.filter_apply, Finsupp.comapDomain.addMonoidHom_apply,
      Finsupp.comapDomain_apply]
  have hle : fullVertex m δ ≤ γ := by
    intro x
    cases x with
    | inl i => simp [fullVertex_inl]
    | inr j => rw [fullVertex_inr, hδ]; split <;> omega
  have hdeg : δ.degree ≤ Q := by
    have hd := Finsupp.degree_mono hle
    rw [fullVertex, Finsupp.degree_mapDomain] at hd
    exact hd.trans hγ
  have hs : ∀ j, δ j ≠ 0 → essential a b j := by
    intro j hj
    by_contra hn
    exact hj (by rw [hδ, if_neg hn])
  have hdiag : inDiagram a b δ := by
    obtain ⟨j, hj, hjγ⟩ := hdiagram
    refine ⟨j, hj, ?_⟩
    intro k
    by_cases hk : essential a b k
    · rw [hδ, if_pos hk]
      simpa [fullVertex_inr] using hjγ (Sum.inr k)
    · have hz : a j k = 0 := by
        by_contra hn
        exact hk ⟨j, hj, Nat.pos_of_ne_zero hn⟩
      rw [hz]
      exact Nat.zero_le _
  have heq : fullVertex m δ + (γ - fullVertex m δ) = γ := add_tsub_cancel_of_le hle
  rw [← heq, partial_add]
  apply partial_complement_mem a _ ?_ (hsupported δ hdeg hs hdiag)
  intro j hj
  simp [fullVertex_inr, hδ, hj]

open Classical in
/-- Recover the transverse ideals and every lower derivative, with block-dependent choices.

Proof (the five DAG steps):
1. Induct on the distinct positive degrees. Monotonicity carries the conclusions for
   earlier blocks into the current ideal; before the first block the variable ideal is zero.
2. For a diagram exponent below the current degree, choose a vertex below it. That vertex
   belongs to an earlier block. Restrict the exponent to that block's essential variables.
   The later-generator hypothesis puts this derivative in the earlier variable ideal.
   Complementary partials preserve that ideal by Leibniz; the coefficient formula for
   formal partials shows they commute. In the first block no such exponent exists.
3. Apply the reduction relation to every exponent outside the diagram. Its diagram terms
   are in the earlier variable ideal by step 2, hence in the current ideal. This treats all
   lower derivatives of current generators; earlier generators were handled in step 1.
   Each selected derivative has degree d_i-1, so it too belongs to the current ideal.
4. Apply the zero-graph matrix-factorization clause of
   lem-trf-formal-transverse-shift-calculus, regrouping all complementary coordinates as W.
   Membership of the selected derivatives in the variable ideal makes their restrictions
   to zero transverse coordinates vanish. Their nonsingular constant Jacobian gives an
   invertible formal matrix factoring them through the coordinate tuple. Thus their ideal
   equals the transverse ideal, proving the other induction assertion. Empty matrices work.
5. For a nonempty generator family take the last degree block, the maximum degree. For an
   empty family there are no blocks or lower derivatives. Positivity makes b-1 nonnegative.
   Neither supported generation nor a Taylor-matrix presentation is used.

Source: Bierstone--Milman, Invent. Math. 128 (1997), Remark 7.16, Lemma 7.17,
and Theorem 7.14, pp.267--268; ILO VIII 2.3.11--2.3.13 for the route
(blueprint: lem-trf-block-low-derivative-recovery). -/
theorem blockLowDerivativeRecovery
    {L : Type u} [Field L] [CharZero L] {m n s : ℕ}
    (a : Fin s → Fin n →₀ ℕ)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hpositive : ∀ i : Fin s, 0 < (a i).degree)
    (horder : ∀ i : Fin s, (f i).order = ((a i).degree : ℕ∞))
    (hincomparable : ∀ i j : Fin s, a i ≤ a j → i = j)
    (hdegree : ∀ i j : Fin s, i < j → (a i).degree ≤ (a j).degree)
    (pick : ∀ b : ℕ, {j : Fin n // essential a b j} → Fin s)
    (β : ∀ b : ℕ, {j : Fin n // essential a b j} → Fin n →₀ ℕ)
    (hchoices : ∀ b : ℕ, (∃ i : Fin s, (a i).degree = b) →
      ∀ j : {j : Fin n // essential a b j},
        (a (pick b j)).degree ≤ b ∧
        a (pick b j) = β b j + Finsupp.single j.val 1 ∧
        iteratedPartial (fullVertex m (β b j)) (f (pick b j)) ∈ transverseIdeal a b)
    (hjacobian : ∀ b : ℕ, (∃ i : Fin s, (a i).degree = b) →
      Matrix.det (fun j l : {j : Fin n // essential a b j} =>
        MvPowerSeries.constantCoeff (MvPowerSeries.pderiv L (Sum.inr l.val)
          (iteratedPartial (fullVertex m (β b j)) (f (pick b j))))) ≠ 0)
    (Q : ℕ) (hQ : ∀ i : Fin s, (a i).degree - 1 ≤ Q)
    (hlater : ∀ b : ℕ, (∃ i : Fin s, (a i).degree = b) →
      ∀ i : Fin s, b < (a i).degree → ∀ δ : Fin n →₀ ℕ,
        δ.degree ≤ Q → (∀ j : Fin n, δ j ≠ 0 → essential a b j) →
        inDiagram a b δ →
        iteratedPartial (fullVertex m δ) (f i) ∈ transverseIdeal a b)
    (I : ℕ → Ideal (MvPowerSeries (Fin m ⊕ Fin n) L)) (hI : Monotone I)
    (hreduction : ∀ (i : Fin s) (t : ℕ), t < (a i).degree →
      ∀ γ : (Fin m ⊕ Fin n) →₀ ℕ,
        (¬ ∃ j : Fin s, fullVertex m (a j) ≤ γ) → γ.degree ≤ t →
        iteratedPartial γ (f i) ∈ I t ⊔
          Ideal.span {h | ∃ α : (Fin m ⊕ Fin n) →₀ ℕ,
            (∃ j : Fin s, fullVertex m (a j) ≤ α) ∧ α.degree ≤ t ∧
              h = iteratedPartial α (f i)}) :
    (∀ b : ℕ, (∃ i : Fin s, (a i).degree = b) →
      (Ideal.span (Set.range (fun j : {j : Fin n // essential a b j} =>
        iteratedPartial (fullVertex m (β b j)) (f (pick b j)))) = transverseIdeal a b ∧
        transverseIdeal (m := m) (R := L) a b ≤ I (b - 1)) ∧
      Ideal.span {h | ∃ (i : Fin s) (ν : (Fin m ⊕ Fin n) →₀ ℕ),
        (a i).degree ≤ b ∧ ν.degree < (a i).degree ∧
          h = iteratedPartial ν (f i)} ≤ I (b - 1)) ∧
    (0 < s →
      Ideal.span {h | ∃ (i : Fin s) (ν : (Fin m ⊕ Fin n) →₀ ℕ),
        ν.degree < (a i).degree ∧ h = iteratedPartial ν (f i)} ≤
          I ((Finset.univ.sup (fun i : Fin s => (a i).degree)) - 1))  := by
  classical
  -- The argument only needs the stated reduction and later-generator hypotheses.
  have _ := horder
  have _ := hincomparable
  have _ := hdegree
  have hblocks : ∀ b : ℕ, (∃ i : Fin s, (a i).degree = b) →
      (Ideal.span (Set.range (fun j : {j : Fin n // essential a b j} ↦
        iteratedPartial (fullVertex m (β b j)) (f (pick b j)))) = transverseIdeal a b ∧
        transverseIdeal (m := m) (R := L) a b ≤ I (b - 1)) ∧
      Ideal.span {h | ∃ (i : Fin s) (ν : (Fin m ⊕ Fin n) →₀ ℕ),
        (a i).degree ≤ b ∧ ν.degree < (a i).degree ∧
          h = iteratedPartial ν (f i)} ≤ I (b - 1) := by
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hb
      have hcurrent (i : Fin s) (hi : (a i).degree = b)
          (ν : (Fin m ⊕ Fin n) →₀ ℕ) (hν : ν.degree < (a i).degree) :
          iteratedPartial ν (f i) ∈ I (b - 1) := by
        have hinside (γ : (Fin m ⊕ Fin n) →₀ ℕ) (hγ : γ.degree ≤ b - 1)
            (hd : ∃ j : Fin s, fullVertex m (a j) ≤ γ) :
            iteratedPartial γ (f i) ∈ I (b - 1) := by
          obtain ⟨j, hj⟩ := hd
          have hjdeg : (a j).degree ≤ γ.degree := by
            simpa only [fullVertex, Finsupp.degree_mapDomain] using Finsupp.degree_mono hj
          have hjb : (a j).degree < b := by have := hpositive i; omega
          have hmem := partial_diagram_mem a (f i)
            (hlater (a j).degree ⟨j, rfl⟩ i (by omega)) γ
            (by have := hQ i; omega) ⟨j, le_rfl, hj⟩
          exact hI (Nat.sub_le_sub_right (Nat.le_of_lt hjb) 1)
            ((ih (a j).degree hjb ⟨j, rfl⟩).1.2 hmem)
        have hνb : ν.degree ≤ b - 1 := by omega
        by_cases hd : ∃ j : Fin s, fullVertex m (a j) ≤ ν
        · exact hinside ν hνb hd
        · have hred := hreduction i (b - 1) (by have := hpositive i; omega) ν hd hνb
          have hspan : Ideal.span {h | ∃ α : (Fin m ⊕ Fin n) →₀ ℕ,
              (∃ j : Fin s, fullVertex m (a j) ≤ α) ∧ α.degree ≤ b - 1 ∧
                h = iteratedPartial α (f i)} ≤ I (b - 1) := by
            apply Ideal.span_le.mpr
            rintro _ ⟨α, hα, hαb, rfl⟩
            exact hinside α hαb hα
          exact (sup_le le_rfl hspan) hred
      have hlow : Ideal.span {h | ∃ (i : Fin s) (ν : (Fin m ⊕ Fin n) →₀ ℕ),
          (a i).degree ≤ b ∧ ν.degree < (a i).degree ∧
            h = iteratedPartial ν (f i)} ≤ I (b - 1) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i, ν, hi, hν, rfl⟩
        by_cases heq : (a i).degree = b
        · exact hcurrent i heq ν hν
        · have hlt : (a i).degree < b := lt_of_le_of_ne hi heq
          apply hI (Nat.sub_le_sub_right hi 1)
          apply (ih (a i).degree hlt ⟨i, rfl⟩).2
          exact Ideal.subset_span ⟨i, ν, le_rfl, hν, rfl⟩
      have heq := coordinate_jacobian_span a
        (fun j : {j : Fin n // essential a b j} ↦
          iteratedPartial (fullVertex m (β b j)) (f (pick b j)))
        (fun j ↦ (hchoices b hb j).2.2) (hjacobian b hb)
      refine ⟨⟨heq, ?_⟩, hlow⟩
      rw [← heq]
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply hlow
      apply Ideal.subset_span
      refine ⟨pick b j, fullVertex m (β b j), (hchoices b hb j).1, ?_, rfl⟩
      have hd := congrArg Finsupp.degree (hchoices b hb j).2.1
      simp only [map_add, Finsupp.degree_single] at hd
      simpa only [fullVertex, Finsupp.degree_mapDomain] using (by omega :
        (β b j).degree < (a (pick b j)).degree)
  refine ⟨hblocks, ?_⟩
  intro hs
  have hnonempty : (Finset.univ : Finset (Fin s)).Nonempty :=
    ⟨⟨0, hs⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hnonempty (fun i : Fin s ↦ (a i).degree)
  apply le_trans ?_ (hblocks _ ⟨i, hi.symm⟩).2
  apply Ideal.span_mono
  rintro h ⟨j, ν, hν, rfl⟩
  exact ⟨j, ν, Finset.le_sup (f := fun i : Fin s ↦ (a i).degree) (Finset.mem_univ j), hν, rfl⟩

end AlgebraicGeometry.HilbertCoefficient
