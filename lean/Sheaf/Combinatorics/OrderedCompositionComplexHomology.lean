module

public import Sheaf.Combinatorics.ProductChainProperIntervalHomology
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Ordered vector-composition complexes

Source: latest blueprint, six-functors basics, direct-images proof paragraph (3),
agent-formulated finite combinatorial input to the rational polynomial-bar calculation
(blueprint: lem-sfb-ordered-composition-complex-homology).

The basis, adjacent-merge differential, rational dual and cumulative-sum comparison
are actual constructions. Only their properties are postponed. The proper-interval
chains and their boundary are the published ProductChainProperInterval constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe w

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace OrderedCompositionComplex

/-- Ordered nonzero blocks summing to m; the empty array is allowed precisely when m = 0.
Source: the basis V_(m,n) in the combinatorial input below direct-images paragraph (3)
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
abbrev Basis {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :=
  {c : Fin n → (Fin r → ℕ) // (∀ a, c a ≠ 0) ∧ ∑ a, c a = m}

/-- The rational vector space on the displayed ordered-composition basis.
Source: V_(m,n), direct-images paragraph (3), combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
abbrev Terms {r : ℕ} (m : Fin r → ℕ) (n : ℕ) := Basis m n →₀ ℚ

/-- Merge adjacent blocks a and a+1, retaining the order of all other blocks.
Source: the displayed merge differential, direct-images paragraph (3), combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def mergeRaw {r n : ℕ} (c : Fin (n + 2) → (Fin r → ℕ)) (a : Fin (n + 1)) :
    Fin (n + 1) → (Fin r → ℕ) :=
  fun j ↦ if j = a then c a.castSucc + c a.succ else c (a.castSucc.succAbove j)

/-- Merging preserves the nonzero-block and total-sum conditions.
Source: proof steps 1 and 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: a sum of two nonzero vectors with natural coordinates is nonzero. The other
blocks are unchanged. Splitting the finite sum at the merged pair gives the original
sum, namely m. -/
theorem merge_valid {r n : ℕ} (m : Fin r → ℕ) (c : Basis m (n + 2))
    (a : Fin (n + 1)) :
    (∀ j, mergeRaw c.val a j ≠ 0) ∧ ∑ j, mergeRaw c.val a j = m := by
  classical
  constructor
  · intro j
    by_cases h : j = a
    · subst j
      simp only [mergeRaw, ↓reduceIte]
      intro hz
      apply c.property.1 a.castSucc
      funext i
      have hi := congrFun hz i
      change c.val a.castSucc i + c.val a.succ i = 0 at hi
      exact (Nat.add_eq_zero_iff.mp hi).1
    · simpa only [mergeRaw, if_neg h] using c.property.1 (a.castSucc.succAbove j)
  · calc
      ∑ j, mergeRaw c.val a j =
          ∑ j, ((if j = a then c.val a.castSucc else 0) +
            c.val (a.castSucc.succAbove j)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = a <;> simp [mergeRaw, h]
      _ = c.val a.castSucc + ∑ j, c.val (a.castSucc.succAbove j) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ j, c.val j := (Fin.sum_univ_succAbove c.val a.castSucc).symm
      _ = m := c.property.2

/-- The adjacent merge as a map of basis sets.
Source: the merge differential in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def merge {r n : ℕ} (m : Fin r → ℕ) (c : Basis m (n + 2)) (a : Fin (n + 1)) :
    Basis m (n + 1) :=
  ⟨mergeRaw c.val a, merge_valid m c a⟩

/-- The differential from degree n+1 to n, zero for n=0. For n+2 blocks the
zero-based merge position a has the required coefficient (-1)^(a+1).
Source: the displayed differential, direct-images paragraph (3), combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def boundary {r : ℕ} (m : Fin r → ℕ) :
    (n : ℕ) → Terms m (n + 1) →ₗ[ℚ] Terms m n
  | 0 => 0
  | n + 1 => Finsupp.linearCombination ℚ fun c ↦
      ∑ a : Fin (n + 1), Finsupp.single (merge m c a) ((-1 : ℚ) ^ (a.val + 1))

/-- Partial sums of the first a+1 blocks in an array with n+1 blocks.
Source: the displayed cumulative-sum formula in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def partialSums {r n : ℕ} (c : Fin (n + 1) → (Fin r → ℕ)) (a : Fin n) :
    Fin r → ℕ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin (n + 1) ↦ b.val ≤ a.val), c b

/-- Partial sums lie in the proper interval and increase strictly.
Source: proof step 2 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: each partial sum is at most m. Its first block makes it nonzero, and the
remaining nonzero blocks prevent it from being m. The difference between two ordered
partial sums is a sum of nonzero intervening blocks, hence is nonzero. -/
theorem partialSums_valid {r n : ℕ} (m : Fin r → ℕ) (c : Basis m (n + 1)) :
    (∀ a, partialSums c.val a ≤ m ∧ partialSums c.val a ≠ 0 ∧
      partialSums c.val a ≠ m) ∧ StrictMono (partialSums c.val) := by
  classical
  have hpos (b : Fin (n + 1)) : (0 : Fin r → ℕ) < c.val b :=
    lt_of_le_of_ne (fun i ↦ Nat.zero_le _) (Ne.symm (c.property.1 b))
  have htop (a : Fin n) : partialSums c.val a < m := by
    have h : partialSums c.val a < ∑ b, c.val b := by
      apply Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _)
        (Finset.mem_univ (Fin.last n))
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
        omega
      · exact hpos (Fin.last n)
      · intro _ _ _
        exact fun i ↦ Nat.zero_le _
    exact h.trans_eq c.property.2
  constructor
  · intro a
    refine ⟨(htop a).le, ?_, (htop a).ne⟩
    intro hz
    apply c.property.1 0
    apply le_antisymm
    · calc
        c.val 0 ≤ partialSums c.val a := by
          apply Finset.single_le_sum (fun _ _ i ↦ Nat.zero_le _)
          simp
        _ = 0 := hz
    · exact fun i ↦ Nat.zero_le _
  · intro a b hab
    apply Finset.sum_lt_sum_of_subset
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.trans (Nat.le_of_lt hab)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ b.castSucc, le_rfl⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
      exact Nat.not_le_of_lt hab
    · exact hpos b.castSucc
    · intro _ _ _
      exact fun i ↦ Nat.zero_le _

/-- Cumulative sums as the canonical map into the published strict-chain basis.
Source: the displayed comparison in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def cumulative {r n : ℕ} (m : Fin r → ℕ) (c : Basis m (n + 1)) :
    ProductChainProperInterval.ChainBasis m n :=
  OrderEmbedding.ofStrictMono
    (fun a ↦ ⟨partialSums c.val a, (partialSums_valid m c).1 a⟩)
    (fun _a _b h ↦ (partialSums_valid m c).2 h)

/-- Extend cumulative sums linearly on the displayed bases.
Source: F_n in proof steps 2 and 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def cumulativeLinear {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    Terms m (n + 1) →ₗ[ℚ] ProductChainProperInterval.Chains m n :=
  Finsupp.linearCombination ℚ fun c ↦ Finsupp.single (cumulative m c) 1

/-- The cumulative comparison is bijective and reverses the boundary sign.
Source: proof steps 2 and 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: invert a strict chain by successive coordinatewise differences, including the
first vertex and m minus the last. These are nonzero and telescope to m. For the
empty chain use the single block m, allowed because m is nonzero. Merging blocks at
one-based position a deletes vertex a-1, giving precisely the negative sign. At two
blocks this says that the merge is minus the augmentation; at one block both maps
out are zero. Extend the basis bijections and identities linearly. -/
theorem cumulative_comparison {r : ℕ} (m : Fin r → ℕ) (hm : m ≠ 0) :
    (∀ n : ℕ, Function.Bijective (cumulativeLinear m n)) ∧
    (∀ n : ℕ, (cumulativeLinear m n).comp (boundary m (n + 1)) =
      -((ProductChainProperInterval.boundary m n).comp (cumulativeLinear m (n + 1)))) := by
  sorry

/-- Adjacent merging squares to zero, including degrees zero and one.
Source: proof step 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: on a basis tuple, two disjoint merges occur in two orders with opposite signs;
for three consecutive blocks the two parenthesizations also have opposite signs and
agree by associativity. Every twice-merged tuple cancels. The low-degree cases are zero.
Equivalently, cumulative sums transport the differential to minus alternating deletion. -/
theorem boundary_squared {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    (OrderedCompositionComplex.boundary (r := r) m n).comp
        (OrderedCompositionComplex.boundary (r := r) m (n + 1)) =
      (0 : OrderedCompositionComplex.Terms (r := r) m (n + 2) →ₗ[ℚ]
        OrderedCompositionComplex.Terms (r := r) m n) := by
  classical
  by_cases hm : m = 0
  · subst m
    have hempty : IsEmpty (Basis (0 : Fin r → ℕ) (n + 2)) := by
      refine ⟨fun c ↦ c.property.1 0 ?_⟩
      apply le_antisymm
      · calc
          c.val 0 ≤ ∑ j, c.val j :=
            Finset.single_le_sum (fun _ _ i ↦ Nat.zero_le _) (Finset.mem_univ 0)
          _ = 0 := c.property.2
      · exact fun i ↦ Nat.zero_le _
    let := hempty
    apply LinearMap.ext
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · cases n with
    | zero => simp [boundary]
    | succ n =>
      have hf (j : ℕ) (y : Terms m (j + 2)) :
          cumulativeLinear m j (boundary m (j + 1) y) =
            -(ProductChainProperInterval.boundary m j (cumulativeLinear m (j + 1) y)) :=
        congrArg (fun f ↦ f y) ((cumulative_comparison m hm).2 j)
      apply LinearMap.ext
      intro x
      apply ((cumulative_comparison m hm).1 n).injective
      change cumulativeLinear m n (boundary m (n + 1) (boundary m (n + 2) x)) =
        cumulativeLinear m n 0
      rw [hf n, hf (n + 1), map_neg, neg_neg, map_zero]
      exact congrArg (fun f ↦ f (cumulativeLinear m (n + 2) x))
        (ProductChainProperInterval.boundary_squared m n)

/-- V_m with natural grading, using exactly the displayed basis and merge maps.
Source: V_m, direct-images paragraph (3), combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def complexNat {r : ℕ} (m : Fin r → ℕ) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℚ (Terms m n))
    (fun n ↦ ModuleCat.ofHom (boundary m n))
    (fun n ↦ congrArg ModuleCat.ofHom (boundary_squared m n))

/-- Preserve nonnegative degrees when extending a chain complex to integer grading.
Source: the extension-by-zero convention in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def natDegreeEmbedding : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℤ) where
  f n := (n : ℤ)
  injective_f := by intro a b h; dsimp at h; omega
  rel := by intro a b h; simp only [ComplexShape.down_Rel] at h ⊢; omega

/-- V_m extended by zero in negative degrees.
Source: V_(m,n)=0 for n<0 in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def complex {r : ℕ} (m : Fin r → ℕ) : ChainComplex (ModuleCat ℚ) ℤ :=
  (complexNat m).extend natDegreeEmbedding

/-- The dual differential is plain precomposition, with no additional sign.
Source: the definition of V_m^* in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def dualBoundary {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    Module.Dual ℚ (Terms m n) →ₗ[ℚ] Module.Dual ℚ (Terms m (n + 1)) :=
  (boundary m n).dualMap

/-- The transposed differential also squares to zero.
Source: proof step 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: evaluating the composite on a functional and a vector is evaluation of that
functional on two consecutive boundaries, which is zero by boundary_squared. -/
theorem dualBoundary_squared {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    (dualBoundary m (n + 1)).comp (dualBoundary m n) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro x
  change f (boundary m n (boundary m (n + 1) x)) = 0
  have h := congrArg (fun d ↦ d x) (boundary_squared m n)
  change boundary m n (boundary m (n + 1) x) = 0 at h
  rw [h, map_zero]

/-- The actual rational dual cochain complex in nonnegative degrees.
Source: V_m^* in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def dualComplex {r : ℕ} (m : Fin r → ℕ) : CochainComplex (ModuleCat ℚ) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℚ (Module.Dual ℚ (Terms m n)))
    (fun n ↦ ModuleCat.ofHom (dualBoundary m n))
    (fun n ↦ congrArg ModuleCat.ofHom (dualBoundary_squared m n))

/-- Terms of A(m) shifted up two degrees: zero at zero, empty chains at one.
Source: A(m)_(n-2) in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def IntervalBasis {r : ℕ} (m : Fin r → ℕ) : ℕ → Type
  | 0 => Fin 0
  | n + 1 => ProductChainProperInterval.ChainBasis m n

/-- Rational free modules on the shifted interval bases.
Source: A(m)_(n-2) in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
abbrev IntervalTerms {r : ℕ} (m : Fin r → ℕ) (n : ℕ) := IntervalBasis m n →₀ ℚ

/-- The shifted interval has its original displayed boundary, including augmentation.
Source: A(m)_(n-2) in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def intervalBoundary {r : ℕ} (m : Fin r → ℕ) :
    (n : ℕ) → IntervalTerms m (n + 1) →ₗ[ℚ] IntervalTerms m n
  | 0 => 0
  | n + 1 => ProductChainProperInterval.boundary m n

/-- The original interval boundary still squares to zero after shifting indices.
Source: proof step 3 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: the bottom composite contains a zero map. Every other composite is exactly
ProductChainProperInterval.boundary_squared, since neither signs nor maps change. -/
theorem intervalBoundary_squared {r : ℕ} (m : Fin r → ℕ) (n : ℕ) :
    (intervalBoundary m n).comp (intervalBoundary m (n + 1)) = 0 := by
  cases n with
  | zero => simp [intervalBoundary]
  | succ n => exact ProductChainProperInterval.boundary_squared m n

/-- A(m) shifted up two degrees, retaining its displayed deletion differential.
Source: the comparison target A(m)_(n-2) in the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology). -/
def intervalComplex {r : ℕ} (m : Fin r → ℕ) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of ℚ (IntervalTerms m n))
    (fun n ↦ ModuleCat.ofHom (intervalBoundary m n))
    (fun n ↦ congrArg ModuleCat.ofHom (intervalBoundary_squared m n))

/-- The sign-corrected cumulative comparison is an isomorphism of complexes and
its image is an isomorphism in the derived category, with the same canonical map.
Source: proof steps 2--4 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: multiply F_n by (-1)^n. The minus-boundary identity becomes the chain-map
identity. Bijectivity in each positive degree, and the two zero terms in degree zero
when m is nonzero, give an isomorphism e. Reindex C_n as C^(-n) by extension along
embeddingDownNat. Apply the derived localization functor to e and its inverse;
functoriality preserves both inverse identities. -/
theorem comparison {r : ℕ} (m : Fin r → ℕ) (hm : m ≠ 0)
    [HasDerivedCategory.{w} (ModuleCat.{0} ℚ)] :
    ∃ e : complexNat m ≅ intervalComplex m,
      (∀ n : ℕ, e.hom.f (n + 1) =
        ModuleCat.ofHom (((-1 : ℚ) ^ (n + 1)) • cumulativeLinear m n)) ∧
      ∃ d : DerivedCategory.Q.obj ((complexNat m).extend ComplexShape.embeddingDownNat) ≅
          DerivedCategory.Q.obj ((intervalComplex m).extend ComplexShape.embeddingDownNat),
        d = DerivedCategory.Q.mapIso
          ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℚ)).mapIso e) := by
  classical
  let f : (n : ℕ) → Terms m n →ₗ[ℚ] IntervalTerms m n
    | 0 => 0
    | n + 1 => ((-1 : ℚ) ^ (n + 1)) • cumulativeLinear m n
  have hbij (n : ℕ) : Function.Bijective (f n) := by
    cases n with
    | zero =>
      have hempty : IsEmpty (Basis m 0) := by
        refine ⟨fun c ↦ hm ?_⟩
        simpa using c.property.2.symm
      let := hempty
      change Function.Bijective (0 : Terms m 0 →ₗ[ℚ] (Fin 0 →₀ ℚ))
      constructor
      · intro x y _
        exact Subsingleton.elim _ _
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩
    | succ n =>
      exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr
        (pow_ne_zero (n + 1) (by norm_num : (-1 : ℚ) ≠ 0)))).comp
          ((cumulative_comparison m hm).1 n)
  let e : complexNat m ≅ intervalComplex m :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ (LinearEquiv.ofBijective (f n) (hbij n)).toModuleIso) (by
        intro i j hij
        have hij' : i = j + 1 := by
          simpa only [ComplexShape.down_Rel, eq_comm] using hij
        subst i
        change ModuleCat.ofHom (f (j + 1)) ≫ (intervalComplex m).d (j + 1) j =
          (complexNat m).d (j + 1) j ≫ ModuleCat.ofHom (f j)
        simp only [complexNat, intervalComplex, ChainComplex.of_d]
        apply ModuleCat.hom_ext
        change (intervalBoundary m j).comp (f (j + 1)) = (f j).comp (boundary m j)
        cases j with
        | zero => simp [intervalBoundary, boundary, f]
        | succ n =>
          apply LinearMap.ext
          intro x
          change ProductChainProperInterval.boundary m n
              (((-1 : ℚ) ^ (n + 2)) • cumulativeLinear m (n + 1) x) =
            ((-1 : ℚ) ^ (n + 1)) • cumulativeLinear m n (boundary m (n + 1) x)
          have hf := congrArg (fun g ↦ g x) ((cumulative_comparison m hm).2 n)
          change cumulativeLinear m n (boundary m (n + 1) x) =
            -(ProductChainProperInterval.boundary m n (cumulativeLinear m (n + 1) x))
              at hf
          rw [hf, map_smul, smul_neg, pow_succ, mul_neg_one, neg_smul])
  refine ⟨e, ?_, ?_⟩
  · intro n
    rfl
  · exact ⟨DerivedCategory.Q.mapIso
      ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat ℚ)).mapIso e), rfl⟩

/-- Finite terms, the complete homology/cohomology dimension formula, and acyclicity.
Source: proof steps 1, 5 and 6 of the same combinatorial input
(blueprint: lem-sfb-ordered-composition-complex-homology).
Proof: all entries of each block lie between zero and m, so the basis is finite.
Each nonzero block contributes at least one to total weight, so n cannot exceed the
sum of the coordinates. For m=0 only the empty tuple remains, including when r=0.
For m nonzero, the cumulative chain isomorphism identifies H_n with the proper
interval homology in degree n-2. Apply lem-sfb-product-chain-proper-interval-homology:
a coordinate at least two gives zero, and a squarefree vector gives one copy of Q
in degree sum m. This includes sum m=1 and interval degree -1. Finally rank-nullity
(lem-weil-pbc-idempotent-charpoly-rank-nullity) and quotient dimensions
(lem-trf-vector-space-quotient-dimension) give dim H_n=c_n-b_n-b_(n+1).
The finite dual dimension and transpose-rank identities
(lem-sfb-linear-dual-dimension-rank) give the identical expression for dim H^n.
Thus the dual dimensions agree, including degree zero where the incoming map is zero. -/
theorem homology {r : ℕ} (m : Fin r → ℕ) :
    (∀ n : ℕ, FiniteDimensional ℚ (Terms m n)) ∧
    (∀ n : ℕ, m ≠ 0 → (∑ i, m i) < n → IsZero ((complexNat m).X n)) ∧
    (∀ n : ℕ,
      Module.finrank ℚ ((dualComplex m).homology n) =
        Module.finrank ℚ ((complexNat m).homology n) ∧
      Module.finrank ℚ ((complexNat m).homology n) =
        if (∀ i, m i = 0 ∨ m i = 1) ∧ n = ∑ i, m i then 1 else 0) ∧
    ((∃ i, 2 ≤ m i) →
      (∀ n : ℕ, IsZero ((complexNat m).homology n)) ∧
      (∀ n : ℕ, IsZero ((dualComplex m).homology n))) := by
  sorry

end OrderedCompositionComplex
