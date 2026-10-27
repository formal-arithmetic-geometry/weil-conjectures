module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Sheaf.Paper.RationalPolynomialBarContraction
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.GroupTheory.Perm.Fin

/-!
# Polynomial additive-bar cofaces and retraction identities

Source: latest blueprint, six-functors basics, direct-images proof paragraph (3),
agent-formulated algebraic obligation, coface/retraction calculation steps 1–8
(blueprint: lem-sfb-polynomial-bar-coface-retraction-identities).

The polynomial modules, differential, ordered inclusion, signed monomial projection,
and extension by zero are the existing `RationalPolynomialBar` constructions.
The contraction theorem is not used. Coordinates and blocks are numbered from zero.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open scoped BigOperators

namespace RationalPolynomialBar

/-- The coface numbered `a`: omit the first block, merge adjacent blocks, or omit
 the last block. Source: the displayed differential and proof steps 1–2 of the
algebraic obligation below latest direct-images paragraph (3)
(blueprint: lem-sfb-polynomial-bar-coface-retraction-identities). -/
def coface (B : Type u) [CommRing B] (r n : ℕ) (a : Fin (n + 2)) :
    P B r n →ₐ[B] P B r (n + 1) :=
  MvPolynomial.aeval fun (b, j) ↦
    if a.val = 0 then MvPolynomial.X (b.succ, j)
    else if b.val + 1 < a.val then MvPolynomial.X (b.castSucc, j)
    else if b.val + 1 = a.val then
      MvPolynomial.X (b.castSucc, j) + MvPolynomial.X (b.succ, j)
    else MvPolynomial.X (b.succ, j)

/-- Each polynomial coordinate has its coordinate unit-vector weight, independently
of the block. Source: multidegree clause and proof step 8 below latest direct-images
paragraph (3) (blueprint: lem-sfb-polynomial-bar-coface-retraction-identities). -/
def coordinateWeight (r n : ℕ) (v : Fin n × Fin r) : Fin r → ℕ :=
  Pi.single v.2 1

/-- The weight of a subset basis vector is its indicator vector.
Source: multidegree clause and proof step 8 below latest direct-images paragraph (3)
(blueprint: lem-sfb-polynomial-bar-coface-retraction-identities). -/
def subsetWeight (r q : ℕ) (I : ExteriorIndex r q) : Fin r → ℕ :=
  fun j ↦ if j ∈ I.val then 1 else 0

/-- A vector in K is homogeneous of weight m precisely when every subset basis
vector with nonzero coefficient has indicator m. Source: the specified grading
of K below latest direct-images paragraph (3), proof step 8
(blueprint: lem-sfb-polynomial-bar-coface-retraction-identities). -/
def ExteriorHomogeneous (B : Type u) [CommRing B] (r q : ℕ)
    (v : K B r q) (m : Fin r → ℕ) : Prop :=
  ∀ I : ExteriorIndex r q, v I ≠ 0 → subsetWeight r q I = m

private theorem coface_X (B : Type u) [CommRing B] (r n : ℕ) (a : Fin (n + 2))
    (b : Fin n) (j : Fin r) :
    coface B r n a (MvPolynomial.X (b, j)) =
      if a.val = 0 then MvPolynomial.X (b.succ, j)
      else if b.val + 1 < a.val then MvPolynomial.X (b.castSucc, j)
      else if b.val + 1 = a.val then
        MvPolynomial.X (b.castSucc, j) + MvPolynomial.X (b.succ, j)
      else MvPolynomial.X (b.succ, j) :=
  MvPolynomial.aeval_X _ _

private theorem coface_comp (B : Type u) [CommRing B] (r n : ℕ)
    (a b : Fin (n + 2)) (hab : a ≤ b) :
    (coface B r (n + 1) b.succ).comp (coface B r n a) =
      (coface B r (n + 1) a.castSucc).comp (coface B r n b) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  have hab' : a.val ≤ b.val := hab
  simp only [AlgHom.comp_apply, coface_X]
  split_ifs <;>
    simp only [map_add, coface_X, Fin.val_succ, Fin.val_castSucc] <;>
    split_ifs
  all_goals try omega
  all_goals first | contradiction | rfl | ac_rfl

private theorem differential_eq_sum (B : Type u) [CommRing B] (r n : ℕ) :
    differential B r n =
      ∑ a : Fin (n + 2), (-1 : B) ^ a.val • (coface B r n a).toLinearMap := by
  classical
  have hfirst : coface B r n 0 =
      MvPolynomial.aeval (fun (b, j) ↦ MvPolynomial.X (b.succ, j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b, j⟩
    simp only [coface_X, MvPolynomial.aeval_X, Fin.val_zero, ite_true]
  have hlast : coface B r n (Fin.last (n + 1)) =
      MvPolynomial.aeval (fun (b, j) ↦ MvPolynomial.X (b.castSucc, j)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b, j⟩
    simp only [coface_X, MvPolynomial.aeval_X, Fin.val_last,
      show n + 1 ≠ 0 by omega, if_false, show b.val + 1 < n + 1 by omega, if_true]
  have hinner (a : Fin n) : coface B r n a.succ.castSucc = merge B r n a := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b, j⟩
    simp only [coface_X, merge, MvPolynomial.aeval_X, Fin.val_castSucc, Fin.val_succ,
      Nat.succ_ne_zero, if_false, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
    simp only [Fin.lt_def, Fin.ext_iff]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero, pow_zero, one_smul,
    Fin.val_last, Fin.castSucc_zero, hfirst, hlast, hinner, differential]

private theorem differential_zero (B : Type u) [CommRing B] (r : ℕ) :
    differential B r 0 = 0 := by
  have h :
      (MvPolynomial.aeval (fun (b, j) ↦ MvPolynomial.X (b.succ, j)) :
        P B r 0 →ₐ[B] P B r 1) =
      MvPolynomial.aeval (fun (b, j) ↦ MvPolynomial.X (b.castSucc, j)) := by
    congr 1
    funext ⟨b, j⟩
    exact Fin.elim0 b
  simp [differential, h]

private theorem negative_terms (B : Type u) [CommRing B] [Algebra ℚ B] (r : ℕ)
    (z : ℤ) (hz : z < 0) :
    CategoryTheory.Limits.IsZero ((polynomialComplex B r).X z) ∧
      CategoryTheory.Limits.IsZero ((exteriorComplex B r).X z) := by
  constructor
  · apply HomologicalComplex.isZero_extend_X
    intro n hn
    change (n : ℤ) = z at hn
    omega
  · apply HomologicalComplex.isZero_extend_X
    intro n hn
    change (n : ℤ) = z at hn
    omega

private theorem exterior_high (B : Type u) [CommRing B] (r q : ℕ) (hq : r < q) :
    Subsingleton (K B r q) := by
  have : IsEmpty (ExteriorIndex r q) := ⟨fun I ↦ by
    have h := Finset.card_le_univ I.val
    simp only [Fintype.card_fin, I.property] at h
    omega⟩
  infer_instance

private theorem rank_zero (B : Type u) [CommRing B] (n : ℕ) (f : P B 0 n) :
    differential B 0 n f =
      if Even n then 0 else MvPolynomial.C (MvPolynomial.coeff 0 f) := by
  rw [MvPolynomial.eq_C_of_isEmpty f]
  have hC (a : Fin (n + 2)) :
      coface B 0 n a (MvPolynomial.C (MvPolynomial.coeff 0 f)) =
        MvPolynomial.C (MvPolynomial.coeff 0 f) := by
    exact MvPolynomial.aeval_C _ _
  rw [differential_eq_sum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, hC,
    ← Finset.sum_smul, Fin.sum_neg_one_pow, Nat.even_add, even_two, iff_true]
  split_ifs <;> simp

private theorem differential_sq (B : Type u) [CommRing B] (r n : ℕ) :
    (differential B r (n + 1)).comp (differential B r n) = 0 := by
  classical
  apply LinearMap.ext
  intro f
  simp only [LinearMap.comp_apply, differential_eq_sum, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    LinearMap.zero_apply]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  let S : Finset (Fin (n + 2) × Fin (n + 3)) :=
    {ij | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij, ij ∈ S → Fin (n + 2) × Fin (n + 3) := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).2 ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, φ, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.val_succ, Fin.val_castLT]
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    apply Prod.ext
    · apply Fin.ext
      have hv := congrArg (fun p : Fin (n + 2) × Fin (n + 3) ↦ p.2.val) h
      simpa only [φ, Fin.val_succ, Nat.add_right_cancel_iff] using hv
    · exact Fin.ext (congrArg (fun p : Fin (n + 2) × Fin (n + 3) ↦ p.1.val) h)
  · rintro ⟨i, j⟩ hij
    have hij' : i.val < j.val := by simpa [S] using hij
    have hj : j ≠ 0 := by intro h; subst j; simp at hij'
    refine ⟨(j.pred hj, i.castSucc), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_castSucc, Fin.val_pred]
      omega
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    have hji : j.val ≤ i.val := (Finset.mem_filter.mp hij).2
    have hc := coface_comp B r n
      (Fin.castLT j (lt_of_le_of_lt hji i.is_lt)) i (by exact hji)
    have hl : (Fin.castLT j (lt_of_le_of_lt hji i.is_lt)).castSucc = j := by
      apply Fin.ext
      rfl
    have hc' := congrArg (fun g : P B r n →ₐ[B] P B r (n + 2) ↦ g f) hc
    simp only [AlgHom.comp_apply, hl] at hc'
    dsimp only [φ]
    simp only [AlgHom.toLinearMap_apply]
    rw [← hc']
    simp only [Fin.val_succ, Fin.val_castLT, pow_succ, mul_neg_one]
    rw [mul_comm]
    simp only [mul_neg, neg_smul, neg_neg]

private theorem aeval_homogeneous (B : Type u) [CommRing B] (r n k : ℕ)
    (g : Fin n × Fin r → P B r k)
    (hg : ∀ x, MvPolynomial.IsWeightedHomogeneous (coordinateWeight r k)
      (g x) (coordinateWeight r n x)) (m : Fin r → ℕ) (f : P B r n)
    (hf : MvPolynomial.IsWeightedHomogeneous (coordinateWeight r n) f m) :
    MvPolynomial.IsWeightedHomogeneous (coordinateWeight r k) (MvPolynomial.aeval g f) m := by
  classical
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa using MvPolynomial.isWeightedHomogeneous_zero B (coordinateWeight r k) m
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ => simpa only [map_add] using ih₁.add ih₂
  | monomial d c hd =>
    rw [MvPolynomial.aeval_monomial]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    rw [← hd, Finsupp.weight_apply]
    exact MvPolynomial.IsWeightedHomogeneous.prod d.support _ _
      (fun x _ ↦ (hg x).pow (d x))

private theorem coface_homogeneous (B : Type u) [CommRing B] (r n : ℕ)
    (a : Fin (n + 2)) (m : Fin r → ℕ) (f : P B r n)
    (hf : MvPolynomial.IsWeightedHomogeneous (coordinateWeight r n) f m) :
    MvPolynomial.IsWeightedHomogeneous (coordinateWeight r (n + 1))
      (coface B r n a f) m := by
  apply aeval_homogeneous B r n (n + 1) _ _ m f hf
  rintro ⟨b, j⟩
  dsimp only
  split_ifs
  all_goals first
    | exact MvPolynomial.isWeightedHomogeneous_X B (coordinateWeight r (n + 1)) _
    | exact (MvPolynomial.isWeightedHomogeneous_X B (coordinateWeight r (n + 1))
        (b.castSucc, j)).add
          (MvPolynomial.isWeightedHomogeneous_X B (coordinateWeight r (n + 1)) (b.succ, j))

private theorem differential_homogeneous (B : Type u) [CommRing B] (r n : ℕ)
    (m : Fin r → ℕ) (f : P B r n)
    (hf : MvPolynomial.IsWeightedHomogeneous (coordinateWeight r n) f m) :
    MvPolynomial.IsWeightedHomogeneous (coordinateWeight r (n + 1))
      (differential B r n f) m := by
  rw [differential_eq_sum, LinearMap.sum_apply]
  apply (MvPolynomial.weightedHomogeneousSubmodule B (coordinateWeight r (n + 1)) m).sum_mem
  intro a _
  exact (MvPolynomial.weightedHomogeneousSubmodule B (coordinateWeight r (n + 1)) m).smul_mem
    _ (coface_homogeneous B r n a m f hf)

private theorem coordinateExponent_apply (r q : ℕ) (j : Fin q → Fin r)
    (a : Fin q) (k : Fin r) :
    coordinateExponent r q j (a, k) = if j a = k then 1 else 0 := by
  classical
  simp only [coordinateExponent, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Prod.mk.injEq, ite_and]
  simp

private theorem coordinateExponent_injective (r q : ℕ) :
    Function.Injective (coordinateExponent r q) := by
  intro j k h
  funext a
  by_contra hne
  have ha := congrArg (fun d ↦ d (a, j a)) h
  have hk : k a ≠ j a := fun hk ↦ hne hk.symm
  simp only [coordinateExponent_apply, ite_true, if_neg hk] at ha
  exact Nat.one_ne_zero ha

private theorem coordinateExponent_weight (r q : ℕ) (j : Fin q → Fin r)
    (hj : Function.Injective j) :
    Finsupp.weight (coordinateWeight r q) (coordinateExponent r q j) =
      subsetWeight r q (coordinateSubset r q j hj) := by
  classical
  simp only [coordinateExponent, map_sum, Finsupp.weight_single, one_nsmul,
    coordinateWeight]
  rw [← Finset.sum_image (f := fun k : Fin r ↦ Pi.single k (1 : ℕ))
    (fun a _ b _ hab ↦ hj hab)]
  ext k
  simp [subsetWeight, coordinateSubset, Pi.single_apply, eq_comm]

private theorem inclusion_homogeneous (B : Type u) [CommRing B] (r q : ℕ)
    (m : Fin r → ℕ) (v : K B r q) (hv : ExteriorHomogeneous B r q v m) :
    MvPolynomial.IsWeightedHomogeneous (coordinateWeight r q) (inclusion B r q v) m := by
  classical
  rw [inclusion, Finsupp.linearCombination_apply, Finsupp.sum]
  apply (MvPolynomial.weightedHomogeneousSubmodule B (coordinateWeight r q) m).sum_mem
  intro I hI
  apply (MvPolynomial.weightedHomogeneousSubmodule B (coordinateWeight r q) m).smul_mem
  have hm := hv I (Finsupp.mem_support_iff.mp hI)
  have hI' : coordinateSubset r q (I.val.orderEmbOfFin I.property)
      (I.val.orderEmbOfFin I.property).injective = I := by
    apply Subtype.ext
    exact I.val.image_orderEmbOfFin_univ I.property
  have hw : Finsupp.weight (coordinateWeight r q)
      (coordinateExponent r q (I.val.orderEmbOfFin I.property)) = subsetWeight r q I := by
    rw [coordinateExponent_weight r q _ (I.val.orderEmbOfFin I.property).injective, hI']
  rw [← hm, ← hw]
  simp only [coordinateExponent, map_sum, Finsupp.weight_single, one_nsmul]
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro a _
  exact MvPolynomial.isWeightedHomogeneous_X B (coordinateWeight r q) _

private theorem projection_monomial (B : Type u) [CommRing B] (r q : ℕ)
    (d : (Fin q × Fin r) →₀ ℕ) :
    projection B r q (MvPolynomial.monomial d 1) = projectMonomial B r q d :=
  (MvPolynomial.basisMonomials (Fin q × Fin r) B).constr_basis B _ d

private theorem projection_coordinate_product (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (hj : Function.Injective j) :
    projection B r q (∏ a : Fin q, MvPolynomial.X (a, j a)) =
      Finsupp.single (coordinateSubset r q j hj) (sortingSign B r q j) := by
  classical
  have hp : (∏ a : Fin q, MvPolynomial.X (a, j a) : P B r q) =
      MvPolynomial.monomial (coordinateExponent r q j) 1 := by
    simp only [coordinateExponent, MvPolynomial.monomial_sum_one,
      ← MvPolynomial.X_pow_eq_monomial, pow_one]
  rw [hp, projection_monomial, projectMonomial]
  rw [Finset.sum_eq_single j]
  · simp only [dif_pos hj, ite_true]
  · intro k _ hkj
    by_cases hk : Function.Injective k
    · simp only [dif_pos hk,
        if_neg (fun h ↦ hkj ((coordinateExponent_injective r q h).symm))]
    · simp only [dif_neg hk]
  · simp

private theorem projection_inclusion (B : Type u) [CommRing B] (r q : ℕ) :
    (projection B r q).comp (inclusion B r q) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext'
  intro I
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, inclusion,
    Finsupp.linearCombination_single, map_smul]
  rw [projection_coordinate_product B r q _ (I.val.orderEmbOfFin I.property).injective]
  have hI : coordinateSubset r q (I.val.orderEmbOfFin I.property)
      (I.val.orderEmbOfFin I.property).injective = I := by
    apply Subtype.ext
    exact I.val.image_orderEmbOfFin_univ I.property
  have hs : sortingSign B r q (I.val.orderEmbOfFin I.property) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    apply Finset.prod_eq_one
    intro b _
    rw [if_neg]
    intro hab
    exact (not_lt_of_ge (le_of_lt ((I.val.orderEmbOfFin I.property).strictMono hab.1)))
      hab.2
  simp only [hI, hs, Finsupp.smul_single, smul_eq_mul, mul_one, LinearMap.id_apply]

private def exteriorWeightSpace (B : Type u) [CommRing B] (r q : ℕ)
    (m : Fin r → ℕ) : Submodule B (K B r q) where
  carrier := {v | ExteriorHomogeneous B r q v m}
  zero_mem' := by
    intro I hI
    exact (hI rfl).elim
  add_mem' := by
    intro v w hv hw I hI
    by_cases h : v I = 0
    · apply hw I
      simpa only [Finsupp.add_apply, h, zero_add] using hI
    · exact hv I h
  smul_mem' := by
    intro c v hv I hI
    exact hv I (right_ne_zero_of_mul hI)

private theorem projection_homogeneous (B : Type u) [CommRing B] (r q : ℕ)
    (m : Fin r → ℕ) (f : P B r q)
    (hf : MvPolynomial.IsWeightedHomogeneous (coordinateWeight r q) f m) :
    ExteriorHomogeneous B r q (projection B r q f) m := by
  classical
  change projection B r q f ∈ exteriorWeightSpace B r q m
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    simpa only [map_add] using (exteriorWeightSpace B r q m).add_mem ih₁ ih₂
  | monomial d c hd =>
    have hc : (MvPolynomial.monomial d c : P B r q) =
        c • MvPolynomial.monomial d 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [hc, map_smul, projection_monomial]
    apply (exteriorWeightSpace B r q m).smul_mem
    unfold projectMonomial
    apply (exteriorWeightSpace B r q m).sum_mem
    intro j _
    split_ifs with hj heq
    · intro I hI
      have hsub : coordinateSubset r q j hj = I := by
        by_contra hne
        simp only [Finsupp.single_apply, if_neg hne] at hI
        exact hI rfl
      rw [← hsub]
      rw [heq, coordinateExponent_weight r q j hj] at hd
      exact hd
    · exact (exteriorWeightSpace B r q m).zero_mem
    · exact (exteriorWeightSpace B r q m).zero_mem

private def omittedProduct (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (k : Fin (q + 1)) : P B r (q + 1) :=
  ∏ b : Fin q, if b.val < k.val then MvPolynomial.X (b.castSucc, j b)
    else MvPolynomial.X (b.succ, j b)

private theorem coface_product_inner (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (a : Fin q) :
    coface B r q a.succ.castSucc (∏ b : Fin q, MvPolynomial.X (b, j b)) =
      omittedProduct B r q j a.castSucc + omittedProduct B r q j a.succ := by
  classical
  let F := fun b : Fin q ↦ coface B r q a.succ.castSucc (MvPolynomial.X (b, j b))
  let G := fun b : Fin q ↦ if b.val < a.val then
    (MvPolynomial.X (b.castSucc, j b) : P B r (q + 1)) else MvPolynomial.X (b.succ, j b)
  let H := fun b : Fin q ↦ if b.val < a.val + 1 then
    (MvPolynomial.X (b.castSucc, j b) : P B r (q + 1)) else MvPolynomial.X (b.succ, j b)
  have hF : F a = G a + H a := by
    simp [F, G, H, coface_X, add_comm]
  have hFG : ∀ b ∈ Finset.univ.erase a, F b = G b := by
    intro b hb
    have hba : b.val ≠ a.val := fun h ↦ (Finset.mem_erase.mp hb).1 (Fin.ext h)
    dsimp only [F, G]
    simp only [coface_X, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> try omega
    all_goals first | contradiction | rfl
  have hHG : ∀ b ∈ Finset.univ.erase a, H b = G b := by
    intro b hb
    have hba : b.val ≠ a.val := fun h ↦ (Finset.mem_erase.mp hb).1 (Fin.ext h)
    dsimp only [H, G]
    split_ifs <;> try omega
    all_goals first | contradiction | rfl
  rw [map_prod]
  change (∏ b, F b) = (∏ b, G b) + ∏ b, H b
  rw [← Finset.mul_prod_erase _ F (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ G (Finset.mem_univ a),
    ← Finset.mul_prod_erase _ H (Finset.mem_univ a), hF,
    Finset.prod_congr rfl hFG, Finset.prod_congr rfl hHG, add_mul]

private theorem differential_coordinate_product (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) :
    differential B r q (∏ a : Fin q, MvPolynomial.X (a, j a)) = 0 := by
  classical
  rw [differential_eq_sum, LinearMap.sum_apply]
  have h := Fin.sum_neg_one_pow_eq_zero
    (fun a : Fin (q + 2) ↦ coface B r q a (∏ b : Fin q, MvPolynomial.X (b, j b)))
    (omittedProduct B r q j)
  have hfirst : coface B r q 0 (∏ b : Fin q, MvPolynomial.X (b, j b)) =
      omittedProduct B r q j 0 := by
    simp only [map_prod, omittedProduct]
    apply Finset.prod_congr rfl
    intro b _
    simp only [coface_X, Fin.val_zero, ite_true, not_lt_zero, ite_false]
  have hlast : coface B r q (Fin.last (q + 1))
      (∏ b : Fin q, MvPolynomial.X (b, j b)) =
      omittedProduct B r q j (Fin.last q) := by
    simp only [map_prod, omittedProduct]
    apply Finset.prod_congr rfl
    intro b _
    simp only [coface_X, Fin.val_last, show q + 1 ≠ 0 by omega, if_false,
      show b.val + 1 < q + 1 by omega, if_true, b.is_lt]
  simpa only [LinearMap.smul_apply, AlgHom.toLinearMap_apply, ← Int.cast_smul_eq_zsmul B,
    Int.cast_pow, Int.cast_neg, Int.cast_one] using
      h hfirst (coface_product_inner B r q j) hlast

private theorem differential_inclusion (B : Type u) [CommRing B] (r q : ℕ) :
    (differential B r q).comp (inclusion B r q) = 0 := by
  apply Finsupp.lhom_ext'
  intro I
  apply LinearMap.ext
  intro c
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, inclusion,
    Finsupp.linearCombination_single, map_smul, differential_coordinate_product,
    smul_zero, LinearMap.zero_apply]

private theorem projection_formula (B : Type u) [CommRing B] (r q : ℕ)
    (f : P B r q) :
    projection B r q f = ∑ j : Fin q → Fin r,
      if hj : Function.Injective j then
        MvPolynomial.coeff (coordinateExponent r q j) f •
          Finsupp.single (coordinateSubset r q j hj) (sortingSign B r q j)
      else 0 := by
  classical
  rw [projection, Module.Basis.constr_apply]
  change (AddMonoidAlgebra.coeff f).sum (fun d c ↦ c • projectMonomial B r q d) = _
  simp only [Finsupp.sum, projectMonomial, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : Function.Injective j
  · simp only [dif_pos hj, smul_ite, smul_zero]
    rw [Finset.sum_eq_single (coordinateExponent r q j)]
    · simp only [ite_true]
      rfl
    · intro d _ hd
      simp only [if_neg hd]
    · intro hn
      have hz : MvPolynomial.coeff (coordinateExponent r q j) f = 0 :=
        MvPolynomial.notMem_support_iff.mp hn
      simp only [ite_true]
      change MvPolynomial.coeff (coordinateExponent r q j) f • _ = 0
      rw [hz, zero_smul]
  · simp only [dif_neg hj, smul_zero, Finset.sum_const_zero]

private theorem projection_rename_omit (B : Type u) [CommRing B] (r q : ℕ)
    (g : Fin q × Fin r → Fin (q + 1) × Fin r) (k : Fin (q + 1))
    (hg : ∀ v, (g v).1 ≠ k) (f : P B r q) :
    projection B r (q + 1) (MvPolynomial.rename g f) = 0 := by
  classical
  rw [projection_formula]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hj
  · have hc : MvPolynomial.coeff (coordinateExponent r (q + 1) j)
        (MvPolynomial.rename g f) = 0 := by
      apply MvPolynomial.coeff_rename_eq_zero
      intro d hd
      have hval := congrArg (fun e ↦ e (k, j k)) hd
      have hz : d.mapDomain g (k, j k) = 0 := by
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨v, hv⟩
        exact hg v (congrArg Prod.fst hv)
      rw [hz, coordinateExponent_apply, if_pos rfl] at hval
      exact (Nat.zero_ne_one hval).elim
    simp only [hc, zero_smul]
  · rfl

private def inversionFactor (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (a b : Fin q) : B :=
  if j a < j b then 1 else if j b < j a then -1 else 0

private theorem inversionFactor_antisymm (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (a b : Fin q) :
    inversionFactor B r q j a b = - inversionFactor B r q j b a := by
  by_cases h : j a < j b
  · simp [inversionFactor, h, not_lt_of_ge h.le]
  · by_cases h' : j b < j a
    · simp [inversionFactor, h, h']
    · simp [inversionFactor, h, h']

private theorem sortingSign_eq_prod (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (hj : Function.Injective j) :
    sortingSign B r q j =
      ∏ a : Fin q, ∏ b ∈ Finset.Ioi a, inversionFactor B r q j a b := by
  classical
  unfold sortingSign
  apply Finset.prod_congr rfl
  intro a _
  symm
  calc
    _ = ∏ b ∈ Finset.Ioi a, (if j b < j a then (-1 : B) else 1) := by
      apply Finset.prod_congr rfl
      intro b hb
      have hab : a < b := Finset.mem_Ioi.mp hb
      have hne : j a ≠ j b := hj.ne hab.ne
      by_cases h : j a < j b
      · simp [inversionFactor, h, not_lt_of_ge h.le]
      · have h' : j b < j a := lt_of_le_of_ne (le_of_not_gt h) hne.symm
        simp [inversionFactor, h, h']
    _ = ∏ b : Fin q, (if a < b ∧ j b < j a then (-1 : B) else 1) := by
      rw [show Finset.Ioi a = Finset.univ.filter (fun b ↦ a < b) by ext; simp]
      simp only [Finset.prod_filter, ite_and]

private theorem sortingSign_comp (B : Type u) [CommRing B] (r q : ℕ)
    (j : Fin q → Fin r) (hj : Function.Injective j) (σ : Equiv.Perm (Fin q)) :
    sortingSign B r q (j ∘ σ) =
      ((σ.sign : ℤ) : B) * sortingSign B r q j := by
  rw [sortingSign_eq_prod B r q (j ∘ σ) (hj.comp σ.injective)]
  change (∏ a : Fin q, ∏ b ∈ Finset.Ioi a, inversionFactor B r q j (σ a) (σ b)) = _
  rw [σ.prod_Ioi_comp_eq_sign_mul_prod (inversionFactor_antisymm B r q j),
    ← sortingSign_eq_prod B r q j hj]

private theorem coordinateSubset_comp (r q : ℕ) (j : Fin q → Fin r)
    (hj : Function.Injective j) (σ : Equiv.Perm (Fin q)) :
    coordinateSubset r q (j ∘ σ) (hj.comp σ.injective) = coordinateSubset r q j hj := by
  apply Subtype.ext
  change Finset.univ.image (j ∘ σ) = Finset.univ.image j
  ext k
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨σ a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨σ.symm a, by simpa only [σ.apply_symm_apply] using ha⟩

private theorem coefficient_rename_blocks (B : Type u) [CommRing B] (r q : ℕ)
    (σ : Equiv.Perm (Fin q)) (j : Fin q → Fin r) (f : P B r q) :
    MvPolynomial.coeff (coordinateExponent r q j)
        (MvPolynomial.rename (fun v : Fin q × Fin r ↦ (σ v.1, v.2)) f) =
      MvPolynomial.coeff (coordinateExponent r q (j ∘ σ)) f := by
  have hg : Function.Injective (fun v : Fin q × Fin r ↦ (σ v.1, v.2)) := by
    rintro ⟨a, i⟩ ⟨b, k⟩ h
    change (σ a, i) = (σ b, k) at h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨σ.injective h.1, h.2⟩
  have hd : (coordinateExponent r q (j ∘ σ)).mapDomain
      (fun v : Fin q × Fin r ↦ (σ v.1, v.2)) = coordinateExponent r q j := by
    simp only [coordinateExponent, Finsupp.mapDomain_finsetSum,
      Finsupp.mapDomain_single, Function.comp_apply]
    exact Equiv.sum_comp σ (fun a ↦ Finsupp.single (a, j a) 1)
  rw [← hd]
  exact MvPolynomial.coeff_rename_mapDomain _ hg f _

private theorem projection_symmetric_zero (B : Type u) [CommRing B] (r q : ℕ)
    (x y : Fin q) (hxy : x ≠ y) (f : P B r q)
    (hf : MvPolynomial.rename
      (fun v : Fin q × Fin r ↦ (Equiv.swap x y v.1, v.2)) f = f) :
    projection B r q f = 0 := by
  classical
  let σ := Equiv.swap x y
  rw [projection_formula]
  apply Finset.sum_involution (fun j _ ↦ j ∘ σ)
  · intro j _
    by_cases hj : Function.Injective j
    · simp only [dif_pos hj, dif_pos (hj.comp σ.injective)]
      have hc := coefficient_rename_blocks B r q σ j f
      rw [hf] at hc
      have hs := sortingSign_comp B r q j hj σ
      simp only [σ, Equiv.Perm.sign_swap hxy, Units.val_neg, Units.val_one,
        Int.cast_neg, Int.cast_one, neg_one_mul] at hs
      rw [coordinateSubset_comp r q j hj σ, hs, ← hc]
      simp only [Finsupp.single_neg, smul_neg, add_neg_cancel]
    · have hj' : ¬ Function.Injective (j ∘ σ) := by
        intro h
        apply hj
        intro a b hab
        have := h (show j (σ (σ.symm a)) = j (σ (σ.symm b)) by simpa using hab)
        exact σ.symm.injective this
      simp only [dif_neg hj, dif_neg hj', add_zero]
  · intro j _ hn heq
    by_cases hj : Function.Injective j
    · have h := congrFun heq x
      have : j y = j x := by simpa only [σ, Function.comp_apply, Equiv.swap_apply_left] using h
      exact hxy (hj this).symm
    · simp only [dif_neg hj] at hn
      exact hn rfl
  · intro j _
    exact Finset.mem_univ _
  · intro j _
    funext a
    simp only [Function.comp_apply, σ, Equiv.swap_apply_self]

private theorem projection_merge (B : Type u) [CommRing B] (r n : ℕ)
    (a : Fin n) (f : P B r n) :
    projection B r (n + 1) (merge B r n a f) = 0 := by
  apply projection_symmetric_zero B r (n + 1) a.castSucc a.succ
    (by intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc,
      Fin.val_succ] at this; omega)
  let g := fun v : Fin (n + 1) × Fin r ↦
    (Equiv.swap a.castSucc a.succ v.1, v.2)
  have heq : (MvPolynomial.rename (R := B) g).comp (merge B r n a) = merge B r n a := by
    apply MvPolynomial.algHom_ext
    rintro ⟨b, j⟩
    simp only [AlgHom.comp_apply, merge, MvPolynomial.aeval_X]
    by_cases hba : b < a
    · have h₁ : b.castSucc ≠ a.castSucc := fun h ↦ hba.ne (Fin.castSucc_injective _ h)
      have h₂ : b.castSucc ≠ a.succ := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        have hab : b.val < a.val := hba
        omega
      simp only [if_pos hba, MvPolynomial.rename_X, g,
        Equiv.swap_apply_of_ne_of_ne h₁ h₂]
    · by_cases hbe : b = a
      · subst b
        simp only [if_neg (lt_irrefl a), ite_true, map_add, MvPolynomial.rename_X,
          g, Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]
      · have h₁ : b.succ ≠ a.castSucc := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_succ] at hv
          have hab : a.val ≤ b.val := le_of_not_gt hba
          omega
        have h₂ : b.succ ≠ a.succ := fun h ↦ hbe (Fin.succ_injective _ h)
        simp only [if_neg hba, if_neg hbe, MvPolynomial.rename_X, g,
          Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  exact congrArg (fun h : P B r n →ₐ[B] P B r (n + 1) ↦ h f) heq

private theorem projection_differential (B : Type u) [CommRing B] (r n : ℕ) :
    (projection B r (n + 1)).comp (differential B r n) = 0 := by
  apply LinearMap.ext
  intro f
  have hfirst : projection B r (n + 1)
      (MvPolynomial.aeval (fun v : Fin n × Fin r ↦ MvPolynomial.X (v.1.succ, v.2)) f) =
        0 := by
    have h := projection_rename_omit B r n
      (fun v : Fin n × Fin r ↦ (v.1.succ, v.2)) 0
      (fun v hv ↦ by have := congrArg Fin.val hv; simp at this) f
    simpa only [MvPolynomial.rename_eq_aeval, Function.comp_def] using h
  have hlast : projection B r (n + 1)
      (MvPolynomial.aeval (fun v : Fin n × Fin r ↦ MvPolynomial.X (v.1.castSucc, v.2)) f) =
        0 := by
    have h := projection_rename_omit B r n
      (fun v : Fin n × Fin r ↦ (v.1.castSucc, v.2)) (Fin.last n)
      (fun v hv ↦ by
        have hval := congrArg Fin.val hv
        simp only [Fin.val_castSucc, Fin.val_last] at hval
        exact (ne_of_lt v.1.is_lt) hval) f
    simpa only [MvPolynomial.rename_eq_aeval, Function.comp_def] using h
  simp only [LinearMap.comp_apply, differential, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_add, map_sum, map_smul,
    hfirst, hlast, projection_merge, smul_zero, Finset.sum_const_zero, add_zero,
    LinearMap.zero_apply]

/-- The coface identities, fixed cochain retraction, multigrading and rank-zero parity.
Source: latest direct-images paragraph (3), agent algebraic obligation, steps 1–8
(blueprint: lem-sfb-polynomial-bar-coface-retraction-identities).

Proof (agent calculation, not a theorem asserted by the blueprint):
1. Polynomial evaluation from `def-weil-pbc-mv-polynomial-ring` gives the cofaces
   as algebra maps. The two degree-zero substitutions fix coefficients, so d⁰=0.
   The given i and p are the linear extensions on their stated free bases.
2. Write formal vertices v₀=0 and vₜ=x₁+⋯+xₜ. Deleting vertex a produces precisely
   coface a on consecutive differences. Deleting vertices a<b in either order
   gives the same substitutions, so polynomial algebra-map extensionality gives
   δᵇδᵃ=δᵃδᵇ⁻¹. The Lean indices are a≤b with the first outer face b+1.
3. Expand d² as a signed double sum. Pair indices (a,b), a<b, with (b-1,a).
   These exhaust all pairs, their composites agree by step 2 and their signs cancel.
4. For the ordered product i(e_I), each inner substitution gives M_a+M_(a+1),
   where M_k omits block k. The two outer terms and all signed inner terms telescope.
   Degree zero uses step 1, and q>r has no subset basis vectors.
5. Express the projection by the coefficients of the one-coordinate-per-block
   monomials. An outer coface omits a block, so all these coefficients vanish.
   An inner coface is invariant under swapping its two merged output blocks.
6. Rewrite the sorting sign as the product over ordered pairs of an antisymmetric
   factor. The permutation-sign product formula shows that a transposition
   negates it. In the projection of a symmetric polynomial, pair each injective
   tuple with its precomposition by that transposition. Their coefficients and
   subset agree, their signs cancel, and neither tuple is fixed. Noninjective
   tuples already contribute zero. Thus every coface has zero projection.
7. The image of i(e_I) has distinct coordinates already sorted, so its projection
   is e_I. This includes the empty subset; for q>r the free module is zero.
8. Substitution preserves coordinate indices, hence all cofaces and d preserve
   weight. Ordered products have weight 1_I; every monomial surviving p has that
   same output weight. No nonzero-ring hypothesis or division was used. When r=0,
   every coface fixes B and the alternating sum is zero in even degrees and the
   identity in odd degrees. The existing integer complexes are extended by zero,
   so all identities extend to negative degrees. -/
theorem coface_retraction_identities (B : Type u) [CommRing B] [Algebra ℚ B] (r : ℕ) :
    (∀ (n : ℕ) (a b : Fin (n + 2)), a ≤ b →
      (coface B r (n + 1) b.succ).comp (coface B r n a) =
        (coface B r (n + 1) a.castSucc).comp (coface B r n b)) ∧
    (∀ n : ℕ, differential B r n =
      ∑ a : Fin (n + 2), (-1 : B) ^ a.val • (coface B r n a).toLinearMap) ∧
    differential B r 0 = 0 ∧
    (∀ n : ℕ, (differential B r (n + 1)).comp (differential B r n) = 0) ∧
    (∀ q : ℕ, (differential B r q).comp (inclusion B r q) = 0) ∧
    (∀ q : ℕ, (projection B r (q + 1)).comp (differential B r q) = 0) ∧
    (∀ q : ℕ, (projection B r q).comp (inclusion B r q) = LinearMap.id) ∧
    (∀ (n : ℕ) (a : Fin (n + 2)) (m : Fin r → ℕ) (f : P B r n),
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r n) f m →
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r (n + 1))
        (coface B r n a f) m) ∧
    (∀ (n : ℕ) (m : Fin r → ℕ) (f : P B r n),
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r n) f m →
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r (n + 1))
        (differential B r n f) m) ∧
    (∀ (q : ℕ) (m : Fin r → ℕ) (v : K B r q),
      ExteriorHomogeneous B r q v m →
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r q) (inclusion B r q v) m) ∧
    (∀ (q : ℕ) (m : Fin r → ℕ) (f : P B r q),
      MvPolynomial.IsWeightedHomogeneous (coordinateWeight r q) f m →
      ExteriorHomogeneous B r q (projection B r q f) m) ∧
    (∀ z : ℤ, z < 0 →
      CategoryTheory.Limits.IsZero ((polynomialComplex B r).X z) ∧
      CategoryTheory.Limits.IsZero ((exteriorComplex B r).X z)) ∧
    (∀ q : ℕ, r < q → Subsingleton (K B r q)) ∧
    (∀ (n : ℕ) (f : P B 0 n), differential B 0 n f =
      if Even n then 0 else MvPolynomial.C (MvPolynomial.coeff 0 f))  := by
  exact ⟨coface_comp B r, differential_eq_sum B r, differential_zero B r,
    differential_sq B r, differential_inclusion B r, projection_differential B r,
    projection_inclusion B r, coface_homogeneous B r, differential_homogeneous B r,
    inclusion_homogeneous B r, projection_homogeneous B r, negative_terms B r,
    exterior_high B r, rank_zero B⟩

end RationalPolynomialBar
