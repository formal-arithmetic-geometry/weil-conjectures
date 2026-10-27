module

public import Sheaf.AlgebraicTopology.IntegralCubicalChainDiagonal
import Sheaf.AlgebraicTopology.CubicalPartitionDifferentialFaces

/-! # Signed cubical partition boundary expansion

Source: the agent-written finite cubical calculation, original diagonal proof steps 2–3,
retained in the DAG (blueprint: lem-sfb-cubical-partition-boundary-expansion).
The current blueprint direct-images proof, paragraph (3), supplies only the route location;
it does not claim this calculation. The DAG's exact external reference remains WANTED.

The chains, standard vectors, partition signs, partition sum and total tensor differential
are the already published constructions. The two definitions below select individual
signed face contributions, before the middle faces cancel.
-/

@[expose] public section

set_option autoImplicit false

namespace IntegralLatticeCubical

/-- The first-factor face at `i` in the partition `(A,C)`, including its shuffle and
boundary signs. Source: original diagonal proof steps 2–3, first displayed face
(blueprint: lem-sfb-cubical-partition-boundary-expansion). -/
noncomputable def partitionFirstFace (r n : ℕ) (v : Fin r → ℤ)
    (A C : Finset (Fin r)) (i : Fin r) :
    (HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).X n :=
  (partitionSign r A C * (-1 : ℤ) ^ (A.filter (fun j ↦ j < i)).card) •
    (tensorCell r n (v + unitVector r i) (v + directionSum r A) (A.erase i) C -
      tensorCell r n v (v + directionSum r A) (A.erase i) C)

/-- The second-factor face at `i` in `(A,C)`, including the tensor differential sign
`(-1)^|A|`. Source: original diagonal proof steps 2–3, second displayed face
(blueprint: lem-sfb-cubical-partition-boundary-expansion). -/
noncomputable def partitionSecondFace (r n : ℕ) (v : Fin r → ℤ)
    (A C : Finset (Fin r)) (i : Fin r) :
    (HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).X n :=
  (partitionSign r A C * (-1 : ℤ) ^ A.card *
      (-1 : ℤ) ^ (C.filter (fun j ↦ j < i)).card) •
    (tensorCell r n v (v + directionSum r A + unitVector r i) A (C.erase i) -
      tensorCell r n v (v + directionSum r A) A (C.erase i))

private theorem inversion_insert_left (r : ℕ) (B C : Finset (Fin r)) (i : Fin r)
    (hi : i ∉ B) :
    (((insert i B).product C).filter (fun p ↦ p.2 < p.1)).card =
      ((B.product C).filter (fun p ↦ p.2 < p.1)).card +
        (C.filter (fun c ↦ c < i)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product,
    Finset.sum_insert hi]
  omega

private theorem inversion_insert_right (r : ℕ) (B C : Finset (Fin r)) (i : Fin r)
    (hi : i ∉ C) :
    ((B.product (insert i C)).filter (fun p ↦ p.2 < p.1)).card =
      ((B.product C).filter (fun p ↦ p.2 < p.1)).card +
        (B.filter (fun b ↦ i < b)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.product_eq_sprod,
    Finset.sum_product,
    Finset.sum_insert hi, Finset.sum_add_distrib]
  omega

private theorem card_below_add_above (r : ℕ) (B : Finset (Fin r)) (i : Fin r)
    (hi : i ∉ B) :
    B.card = (B.filter (fun b ↦ b < i)).card + (B.filter (fun b ↦ i < b)).card := by
  have h : B.filter (fun b ↦ ¬b < i) = B.filter (fun b ↦ i < b) := by
    ext b
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hb, hbi⟩
      exact ⟨hb, lt_of_le_of_ne (le_of_not_gt hbi) (by rintro rfl; exact hi hb)⟩
    · rintro ⟨hb, hbi⟩
      exact ⟨hb, not_lt_of_gt hbi⟩
  rw [← Finset.card_filter_add_card_filter_not (fun b ↦ b < i), h]

private theorem partition_not_mem (r : ℕ) (I B C : Finset (Fin r)) (i : Fin r)
    (h : B ∪ C = I.erase i) : i ∉ B ∧ i ∉ C := by
  have hi : i ∉ B ∪ C := by rw [h]; exact Finset.notMem_erase i I
  simpa only [Finset.mem_union, not_or] using hi

private theorem signs_and_faces (r n : ℕ) (v : Fin r → ℤ)
    (B C : Finset (Fin r)) (i : Fin r) (hiB : i ∉ B) (hiC : i ∉ C) :
    let N := ((B.product C).filter (fun p ↦ p.2 < p.1)).card
    let p := (B.filter (fun b ↦ b < i)).card
    let q := (C.filter (fun c ↦ c < i)).card
    let t := (B.filter (fun b ↦ i < b)).card
    (partitionSign r (insert i B) C *
        (-1 : ℤ) ^ ((insert i B).filter (fun j ↦ j < i)).card = (-1 : ℤ) ^ (N+q+p)) ∧
    ((-1 : ℤ) ^ (N+q+p) = (-1 : ℤ) ^ (p+q) * partitionSign r B C) ∧
    (partitionSign r B (insert i C) * (-1 : ℤ) ^ B.card *
        (-1 : ℤ) ^ ((insert i C).filter (fun j ↦ j < i)).card =
      (-1 : ℤ) ^ (N+t+B.card+q)) ∧
    ((-1 : ℤ) ^ (N+t+B.card+q) = (-1 : ℤ) ^ (p+q) * partitionSign r B C) ∧
    (partitionFirstFace r n v (insert i B) C i =
      ((-1 : ℤ) ^ (p+q) * partitionSign r B C) •
        (tensorCell r n (v + unitVector r i) (v + directionSum r B + unitVector r i) B C -
          tensorCell r n v (v + directionSum r B + unitVector r i) B C)) ∧
    (partitionSecondFace r n v B (insert i C) i =
      ((-1 : ℤ) ^ (p+q) * partitionSign r B C) •
        (tensorCell r n v (v + directionSum r B + unitVector r i) B C -
          tensorCell r n v (v + directionSum r B) B C)) := by
  dsimp only
  have hfirst : partitionSign r (insert i B) C *
      (-1 : ℤ) ^ ((insert i B).filter (fun j ↦ j < i)).card =
      (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
        (C.filter (fun c ↦ c < i)).card + (B.filter (fun b ↦ b < i)).card) := by
    rw [partitionSign, inversion_insert_left r B C i hiB]
    simp only [Finset.filter_insert, lt_self_iff_false, ↓reduceIte, pow_add]
  have hfirst' : (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
      (C.filter (fun c ↦ c < i)).card + (B.filter (fun b ↦ b < i)).card) =
      (-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
        (C.filter (fun c ↦ c < i)).card) * partitionSign r B C := by
    simp only [partitionSign, pow_add]
    ring
  have hsecond : partitionSign r B (insert i C) * (-1 : ℤ) ^ B.card *
      (-1 : ℤ) ^ ((insert i C).filter (fun j ↦ j < i)).card =
      (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
        (B.filter (fun b ↦ i < b)).card + B.card + (C.filter (fun c ↦ c < i)).card) := by
    rw [partitionSign, inversion_insert_right r B C i hiC]
    simp only [Finset.filter_insert, lt_self_iff_false, ↓reduceIte, pow_add]
  have hsecond' : (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
      (B.filter (fun b ↦ i < b)).card + B.card + (C.filter (fun c ↦ c < i)).card) =
      (-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
        (C.filter (fun c ↦ c < i)).card) * partitionSign r B C := by
    rw [card_below_add_above r B i hiB]
    have heven : ((-1 : ℤ) ^ (B.filter (fun b ↦ i < b)).card) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      simp
    simp only [partitionSign, pow_add]
    calc
      _ = ((-1 : ℤ) ^ (B.filter (fun b ↦ i < b)).card) ^ 2 *
          ((-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
            (C.filter (fun c ↦ c < i)).card) * partitionSign r B C) := by
              simp only [partitionSign, pow_add]; ring
      _ = _ := by rw [heven, one_mul]; simp only [partitionSign, pow_add]
  refine ⟨hfirst, hfirst', hsecond, hsecond', ?_, ?_⟩
  · unfold partitionFirstFace
    rw [hfirst, hfirst', Finset.erase_insert hiB]
    simp only [directionSum, Finset.sum_insert hiB]
    abel
  · unfold partitionSecondFace
    rw [hsecond, hsecond', Finset.erase_insert hiC]

private theorem first_index_bij (r : ℕ) (I : Finset (Fin r)) :
    Set.BijOn
      (fun x : Finset (Fin r) × Finset (Fin r) × Fin r ↦
        (x.2.2, x.1.erase x.2.2, x.2.1))
      {x | Disjoint x.1 x.2.1 ∧ x.1 ∪ x.2.1 = I ∧ x.2.2 ∈ x.1}
      {y | y.1 ∈ I ∧ Disjoint y.2.1 y.2.2 ∧ y.2.1 ∪ y.2.2 = I.erase y.1} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨A, C, i⟩ ⟨hd, hu, hi⟩
    have hiC : i ∉ C := fun h ↦ Finset.disjoint_left.mp hd hi h
    refine ⟨?_, hd.mono_left (Finset.erase_subset i A), ?_⟩
    · rw [← hu]
      exact Finset.mem_union_left C hi
    · rw [← hu, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hiC]
  · rintro ⟨A, C, i⟩ hx ⟨A', C', i'⟩ hy heq
    obtain ⟨rfl, hA, rfl⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    have hAA : A = A' := Finset.erase_injOn' i hx.2.2 hy.2.2 hA
    cases hAA
    rfl
  · rintro ⟨i, B, C⟩ ⟨hi, hd, hu⟩
    obtain ⟨hiB, hiC⟩ := partition_not_mem r I B C i hu
    refine ⟨(insert i B, C, i), ⟨?_, ?_, Finset.mem_insert_self i B⟩, ?_⟩
    · exact Finset.disjoint_insert_left.mpr ⟨hiC, hd⟩
    · rw [Finset.insert_union, hu, Finset.insert_erase hi]
    · simp only [Finset.erase_insert hiB]

private theorem second_index_bij (r : ℕ) (I : Finset (Fin r)) :
    Set.BijOn
      (fun x : Finset (Fin r) × Finset (Fin r) × Fin r ↦
        (x.2.2, x.1, x.2.1.erase x.2.2))
      {x | Disjoint x.1 x.2.1 ∧ x.1 ∪ x.2.1 = I ∧ x.2.2 ∈ x.2.1}
      {y | y.1 ∈ I ∧ Disjoint y.2.1 y.2.2 ∧ y.2.1 ∪ y.2.2 = I.erase y.1} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨A, C, i⟩ ⟨hd, hu, hi⟩
    have hiA : i ∉ A := fun h ↦ Finset.disjoint_left.mp hd h hi
    refine ⟨?_, hd.mono_right (Finset.erase_subset i C), ?_⟩
    · rw [← hu]
      exact Finset.mem_union_right A hi
    · rw [← hu, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hiA]
  · rintro ⟨A, C, i⟩ hx ⟨A', C', i'⟩ hy heq
    obtain ⟨rfl, rfl, hC⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    have hCC : C = C' := Finset.erase_injOn' i hx.2.2 hy.2.2 hC
    cases hCC
    rfl
  · rintro ⟨i, B, C⟩ ⟨hi, hd, hu⟩
    obtain ⟨hiB, hiC⟩ := partition_not_mem r I B C i hu
    refine ⟨(B, insert i C, i), ⟨?_, ?_, Finset.mem_insert_self i C⟩, ?_⟩
    · exact Finset.disjoint_insert_right.mpr ⟨hiB, hd⟩
    · rw [Finset.union_insert, hu, Finset.insert_erase hi]
    · simp only [Finset.erase_insert hiC]

/-- Every first and second face has the stated common sign, the two face indexings are
bijective, and cancellation gives the explicit outer-face sum, including the empty case.
Here `(B.filter (· < i)).card`, `(C.filter (· < i)).card`,
`(B.filter (i < ·)).card`, and `((B.product C).filter (fun p ↦ p.2 < p.1)).card`
are respectively the node's `p`, `q`, `t`, and `N`.

Source: the six-step finite-sum proof in the DAG, expanding original diagonal steps 2–3
(blueprint: lem-sfb-cubical-partition-boundary-expansion).

Proof plan:
1. Expand `diagonalComponent` and the total differential using the displayed cubical
boundary from `lem-sfb-integral-lattice-cubical-contraction`. Distribute tensors over sums
by `def-weil-pbc-module-tensor-product`. The first faces have `i` in the first part, the
second faces have `i` in the second part.
2. The first reindexing sends `(A,C,i)` to `(i,A.erase i,C)`, with inverse
`(i,B,C)` sent to `(insert i B,C,i)`. The second sends `(A,C,i)` to `(i,A,C.erase i)`,
with inverse `(i,B,C)` sent to `(B,insert i C,i)`. Disjointness and membership prove that
these are inverse on the displayed sets, including empty sets.
3. The elements of `I` below `i` number `p+q`, and `|B|=p+t`. The inversion count
for `(insert i B,C)` is `N+q` and the face position is `p`. Its coefficient is thus
`(-1)^(N+q+p) = (-1)^(p+q) partitionSign B C`.
4. The inversion count for `(B,insert i C)` is `N+t`, its face position is `q`,
and the tensor sign is `(-1)^|B|`. Its coefficient is `(-1)^(N+t+|B|+q)`;
substitute `|B|=p+t` and remove the even exponent `2t` to obtain the same sign.
5. Since `u_(insert i B)=u_B+u_i`, the first face is the first displayed difference;
the second is the second displayed difference. Tensor bilinearity identifies the common
middle tensor. Its two coefficients are opposite, so it cancels.
6. Sum over the two bijective indexings. Replace `p+q` by the position of `i` in `I`,
and commute `u_B` with `u_i`. This yields the displayed outer-face sum. If `I` is empty,
the unique partition is empty in both factors, both boundaries vanish in degree zero,
and the outer sum is empty. This includes `r=0`.
-/
theorem partitionBoundaryExpansion (r : ℕ) (v : Fin r → ℤ) (I : Finset (Fin r)) :
    (∀ (i : Fin r) (B C : Finset (Fin r)),
      i ∈ I → Disjoint B C → B ∪ C = I.erase i →
      (partitionSign r (insert i B) C *
          (-1 : ℤ) ^ ((insert i B).filter (fun j ↦ j < i)).card =
        (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
          (C.filter (fun c ↦ c < i)).card + (B.filter (fun b ↦ b < i)).card)) ∧
      ((-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
          (C.filter (fun c ↦ c < i)).card + (B.filter (fun b ↦ b < i)).card) =
        (-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
          (C.filter (fun c ↦ c < i)).card) * partitionSign r B C) ∧
      (partitionSign r B (insert i C) * (-1 : ℤ) ^ B.card *
          (-1 : ℤ) ^ ((insert i C).filter (fun j ↦ j < i)).card =
        (-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
          (B.filter (fun b ↦ i < b)).card + B.card + (C.filter (fun c ↦ c < i)).card)) ∧
      ((-1 : ℤ) ^ (((B.product C).filter (fun p ↦ p.2 < p.1)).card +
          (B.filter (fun b ↦ i < b)).card + B.card + (C.filter (fun c ↦ c < i)).card) =
        (-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
          (C.filter (fun c ↦ c < i)).card) * partitionSign r B C) ∧
      (partitionFirstFace r (I.card - 1) v (insert i B) C i =
        ((-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
            (C.filter (fun c ↦ c < i)).card) * partitionSign r B C) •
          (tensorCell r (I.card - 1) (v + unitVector r i)
              (v + directionSum r B + unitVector r i) B C -
            tensorCell r (I.card - 1) v (v + directionSum r B + unitVector r i) B C)) ∧
      (partitionSecondFace r (I.card - 1) v B (insert i C) i =
        ((-1 : ℤ) ^ ((B.filter (fun b ↦ b < i)).card +
            (C.filter (fun c ↦ c < i)).card) * partitionSign r B C) •
          (tensorCell r (I.card - 1) v (v + directionSum r B + unitVector r i) B C -
            tensorCell r (I.card - 1) v (v + directionSum r B) B C))) ∧
    Set.BijOn
      (fun x : Finset (Fin r) × Finset (Fin r) × Fin r ↦
        (x.2.2, x.1.erase x.2.2, x.2.1))
      {x | Disjoint x.1 x.2.1 ∧ x.1 ∪ x.2.1 = I ∧ x.2.2 ∈ x.1}
      {y | y.1 ∈ I ∧ Disjoint y.2.1 y.2.2 ∧ y.2.1 ∪ y.2.2 = I.erase y.1} ∧
    Set.BijOn
      (fun x : Finset (Fin r) × Finset (Fin r) × Fin r ↦
        (x.2.2, x.1, x.2.1.erase x.2.2))
      {x | Disjoint x.1 x.2.1 ∧ x.1 ∪ x.2.1 = I ∧ x.2.2 ∈ x.2.1}
      {y | y.1 ∈ I ∧ Disjoint y.2.1 y.2.2 ∧ y.2.1 ∪ y.2.2 = I.erase y.1} ∧
    ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).d
        I.card (I.card - 1))
      (diagonalComponent r I.card (cell r (I.card : ℤ) v I)) =
      ∑ i ∈ I, ∑ B ∈ (I.erase i).powerset,
        ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card *
            partitionSign r B (I.erase i \ B)) •
          (tensorCell r (I.card - 1) (v + unitVector r i)
              (v + unitVector r i + directionSum r B) B (I.erase i \ B) -
            tensorCell r (I.card - 1) v (v + directionSum r B) B (I.erase i \ B)) ∧
    (I = ∅ →
      ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).d
          I.card (I.card - 1))
        (diagonalComponent r I.card (cell r (I.card : ℤ) v I)) = 0) := by
  have hlocal := fun (i : Fin r) (B C : Finset (Fin r))
      (_hi : i ∈ I) (_hd : Disjoint B C) (hu : B ∪ C = I.erase i) ↦
    signs_and_faces r (I.card - 1) v B C i
      (partition_not_mem r I B C i hu).1 (partition_not_mem r I B C i hu).2
  have hboundary :
      ((HomologicalComplex.tensorObj (chainComplex r) (chainComplex r)).d
          I.card (I.card - 1))
        (diagonalComponent r I.card (cell r (I.card : ℤ) v I)) =
        ∑ i ∈ I, ∑ B ∈ (I.erase i).powerset,
          ((-1 : ℤ) ^ (I.filter (fun j ↦ j < i)).card *
              partitionSign r B (I.erase i \ B)) •
            (tensorCell r (I.card - 1) (v + unitVector r i)
                (v + unitVector r i + directionSum r B) B (I.erase i \ B) -
              tensorCell r (I.card - 1) v (v + directionSum r B) B (I.erase i \ B)) := by
    rw [partitionDifferentialFaces]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro B hB
    have hsub : B ⊆ I.erase i := Finset.mem_powerset.mp hB
    have hu : B ∪ (I.erase i \ B) = I.erase i := Finset.union_sdiff_of_subset hsub
    have hd : Disjoint B (I.erase i \ B) := Finset.disjoint_sdiff
    have hfaces := hlocal i B (I.erase i \ B) hi hd hu
    change partitionFirstFace r (I.card - 1) v (insert i B) (I.erase i \ B) i +
      partitionSecondFace r (I.card - 1) v B (insert i (I.erase i \ B)) i = _
    rw [hfaces.2.2.2.2.1, hfaces.2.2.2.2.2]
    have hpos : (I.filter (fun j ↦ j < i)).card =
        (B.filter (fun b ↦ b < i)).card +
          ((I.erase i \ B).filter (fun c ↦ c < i)).card := by
      have hfilter : I.filter (fun j ↦ j < i) =
          (I.erase i).filter (fun j ↦ j < i) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hj, hji⟩
          exact ⟨⟨ne_of_lt hji, hj⟩, hji⟩
        · rintro ⟨⟨_, hj⟩, hji⟩
          exact ⟨hj, hji⟩
      calc
        _ = ((I.erase i).filter (fun j ↦ j < i)).card := congrArg Finset.card hfilter
        _ = ((B ∪ (I.erase i \ B)).filter (fun j ↦ j < i)).card :=
          congrArg (fun S : Finset (Fin r) ↦ (S.filter (fun j ↦ j < i)).card) hu.symm
        _ = _ := by
          rw [Finset.filter_union,
            Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _)
              (Finset.filter_subset _ _))]
    rw [hpos]
    have hv : v + directionSum r B + unitVector r i =
        v + unitVector r i + directionSum r B := by abel
    rw [hv]
    simp only [zsmul_sub]
    abel
  refine ⟨hlocal, first_index_bij r I, second_index_bij r I, hboundary, ?_⟩
  intro hI
  simpa only [hI, Finset.sum_empty] using hboundary

end IntegralLatticeCubical
