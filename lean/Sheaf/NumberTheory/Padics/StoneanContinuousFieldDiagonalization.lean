/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.ExtremallyDisconnected
import Sheaf.NumberTheory.Padics.StoneanContinuousPivotIsolation

/-!
# Continuous integral diagonalization over Stonean bases

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 6.12(2),
proof on printed p. 19; rectangular matrix variant by clopen selection and bounded division
(blueprint: lem-sfb-stonean-continuous-field-diagonalization).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Padic

private def border {R : Type*} [Zero R] {n m : ℕ}
    (a : R) (B : Matrix (Fin n) (Fin m) R) : Matrix (Fin (n + 1)) (Fin (m + 1)) R :=
  fun i j ↦ Fin.cases (Fin.cases a (fun _ ↦ 0) j)
    (fun i ↦ Fin.cases 0 (B i) j) i

private theorem border_mul {R : Type*} [Semiring R] {n m k : ℕ}
    (a b : R) (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    border a A * border b B = border (a * b) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [border, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem border_one {R : Type*} [Semiring R] {n : ℕ} :
    border (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [border, Matrix.one_apply, eq_comm]

private def borderGL {R : Type*} [Semiring R] {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) R) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) R where
  val := border 1 A.val
  inv := border 1 A.inv
  val_inv := by rw [border_mul, one_mul, A.val_inv, border_one]
  inv_val := by rw [border_mul, one_mul, A.inv_val, border_one]

private theorem border_map {R S : Type*} [Zero R] [Zero S] {n m : ℕ}
    (f : R → S) (hf : f 0 = 0) (a : R) (B : Matrix (Fin n) (Fin m) R) :
    (border a B).map f = border (f a) (B.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j <;>
    simp [border, Matrix.map_apply, hf]

private theorem continuous_entries_mul {R : Type*} [Semiring R]
    [TopologicalSpace R] [IsTopologicalSemiring R] {X : Type*} [TopologicalSpace X]
    {n m k : ℕ} {A : X → Matrix (Fin n) (Fin m) R}
    {B : X → Matrix (Fin m) (Fin k) R}
    (hA : ∀ i j, Continuous (fun x ↦ A x i j))
    (hB : ∀ i j, Continuous (fun x ↦ B x i j)) :
    ∀ i j, Continuous (fun x ↦ (A x * B x) i j) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact continuous_finsetSum _ (fun k _ ↦ (hA i k).mul (hB k j))

private theorem continuous_entries_borderGL {R E : Type*} [CommRing R] [CommRing E]
    [TopologicalSpace E] {X : Type*} [TopologicalSpace X] {n : ℕ}
    (f : R →+* E) {A : X → Matrix.GeneralLinearGroup (Fin n) R}
    (hA : ∀ i j, Continuous (fun x ↦ f ((A x).val i j))) :
    ∀ i j, Continuous (fun x ↦ f ((borderGL (A x)).val i j)) := by
  intro i j
  refine Fin.cases ?_ (fun i ↦ ?_) i <;>
    refine Fin.cases ?_ (fun j ↦ ?_) j
  · change Continuous (fun _ : X ↦ f 1)
    exact continuous_const
  · change Continuous (fun _ : X ↦ f 0)
    exact continuous_const
  · change Continuous (fun _ : X ↦ f 0)
    exact continuous_const
  · exact hA i j

private theorem offDiagonal_induction
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (P : Type v) [TopologicalSpace P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [ExtremallyDisconnected P]
    (n m : ℕ) (F : P → Matrix (Fin n) (Fin m) E)
    (hF : ∀ i j, @Continuous P E _
      (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
      (fun p ↦ F p i j)) :
    ∃ (L : P → Matrix.GeneralLinearGroup (Fin n) (coefficientExtensionIntegers l E))
      (U : P → Matrix.GeneralLinearGroup (Fin m) (coefficientExtensionIntegers l E)),
      (∀ i j, @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((L p).val i j : E))) ∧
      (∀ i j, @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((L p)⁻¹).val i j : E))) ∧
      (∀ i j, @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((U p).val i j : E))) ∧
      (∀ i j, @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((U p)⁻¹).val i j : E))) ∧
      (∀ p i j, i.val ≠ j.val →
        ((L p).val.map (fun x ↦ (x : E)) * F p *
          (U p).val.map (fun x ↦ (x : E))) i j = 0) := by
  classical
  let : NormedField E := spectralNorm.normedField (Padic l) E
  let O := coefficientExtensionIntegers l E
  let f : O →+* E := O.subtype
  induction n generalizing m with
  | zero =>
    refine ⟨fun _ ↦ 1, fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i j; exact continuous_const
    · intro i j; exact continuous_const
    · intro p i; exact Fin.elim0 i
  | succ n ih =>
    cases m with
    | zero =>
      refine ⟨fun _ ↦ 1, fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_⟩
      · intro i j; exact continuous_const
      · intro i j; exact continuous_const
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
      · intro p i j; exact Fin.elim0 j
    | succ m =>
      obtain ⟨S, T, hS, hSi, hT, hTi, hrow, hcol⟩ :=
        exists_continuous_integral_pivot_isolation l E P n m F hF
      let A : P → Matrix (Fin (n + 1)) (Fin (m + 1)) E :=
        fun p ↦ (S p).val.map f * F p * (T p).val.map f
      have hA : ∀ i j, Continuous (fun p ↦ A p i j) :=
        continuous_entries_mul (continuous_entries_mul hS hF) hT
      let B : P → Matrix (Fin n) (Fin m) E := fun p i j ↦ A p i.succ j.succ
      obtain ⟨L, U, hL, hLi, hU, hUi, hdiag⟩ :=
        ih m B (fun i j ↦ hA i.succ j.succ)
      let L₁ := fun p ↦ borderGL (L p)
      let U₁ := fun p ↦ borderGL (U p)
      have hL₁ : ∀ i j, Continuous (fun p ↦ f ((L₁ p).val i j)) :=
        continuous_entries_borderGL f hL
      have hU₁ : ∀ i j, Continuous (fun p ↦ f ((U₁ p).val i j)) :=
        continuous_entries_borderGL f hU
      have hL₁i : ∀ i j, Continuous (fun p ↦ f (((L₁ p)⁻¹).val i j)) :=
        continuous_entries_borderGL f hLi
      have hU₁i : ∀ i j, Continuous (fun p ↦ f (((U₁ p)⁻¹).val i j)) :=
        continuous_entries_borderGL f hUi
      have hmap (V W : Matrix.GeneralLinearGroup (Fin (n + 1)) O) :
          (V * W).val.map f = V.val.map f * W.val.map f := by
        exact Matrix.map_mul
      have hmap' (V W : Matrix.GeneralLinearGroup (Fin (m + 1)) O) :
          (V * W).val.map f = V.val.map f * W.val.map f := by
        exact Matrix.map_mul
      refine ⟨fun p ↦ L₁ p * S p, fun p ↦ T p * U₁ p, ?_, ?_, ?_, ?_, ?_⟩
      · change ∀ i j, Continuous (fun p ↦ ((L₁ p * S p).val.map f) i j)
        simp_rw [hmap]
        exact continuous_entries_mul hL₁ hS
      · change ∀ i j, Continuous (fun p ↦ (((L₁ p * S p)⁻¹).val.map f) i j)
        simp_rw [mul_inv_rev, hmap]
        exact continuous_entries_mul hSi hL₁i
      · change ∀ i j, Continuous (fun p ↦ ((T p * U₁ p).val.map f) i j)
        simp_rw [hmap']
        exact continuous_entries_mul hT hU₁
      · change ∀ i j, Continuous (fun p ↦ (((T p * U₁ p)⁻¹).val.map f) i j)
        simp_rw [mul_inv_rev, hmap']
        exact continuous_entries_mul hU₁i hTi
      · have hblock (p : P) : A p = border (A p 0 0) (B p) := by
          ext i j
          refine Fin.cases ?_ (fun i ↦ ?_) i <;>
            refine Fin.cases ?_ (fun j ↦ ?_) j
          · rfl
          · exact hrow p j
          · exact hcol p i
          · rfl
        have heq (p : P) :
            ((L₁ p * S p).val.map f * F p * (T p * U₁ p).val.map f) =
              border (A p 0 0) ((L p).val.map f * B p * (U p).val.map f) := by
          rw [hmap, hmap']
          calc
            _ = (L₁ p).val.map f * A p * (U₁ p).val.map f := by
              simp only [A, Matrix.mul_assoc]
            _ = _ := by
              change (border 1 (L p).val).map f * A p *
                (border 1 (U p).val).map f = _
              rw [border_map f (map_zero f), border_map f (map_zero f), map_one]
              nth_rw 1 [hblock p]
              rw [border_mul, border_mul, one_mul, mul_one]
        intro p i j hij
        change ((L₁ p * S p).val.map f * F p *
          (T p * U₁ p).val.map f) i j = 0
        rw [heq]
        revert hij
        refine Fin.cases ?_ (fun i ↦ ?_) i <;>
          refine Fin.cases ?_ (fun j ↦ ?_) j
        · exact fun h ↦ (h rfl).elim
        · intro _; rfl
        · intro _; rfl
        · intro h
          exact hdiag p i j (fun he ↦ h (congrArg Nat.succ he))

/-- Every continuous rectangular matrix on a Stonean profinite space has a continuous
integral invertible change of rows and columns to a diagonal matrix. Continuity of integral
entries is expressed after inclusion into the field, equivalently in the subspace topology.
The same condition is required for inverse entries. Diagonal entries may vanish, and no
rank, valuation or elementary-divisor local constancy is assumed.

Source: Hemo--Richarz--Scholbach, Constructible sheaves on schemes, Theorem 6.12(2),
proof on printed p. 19; agent rectangular matrix variant
(blueprint: lem-sfb-stonean-continuous-field-diagonalization).

Proof:
1. For continuous a,b with |a| ≤ |b|, the closed equation space
   Z = {(p,t) in P × O_E : a(p) = b(p)t} is compact Hausdorff. Compactness of O_E is
   lem-sfb-integers-profinite-tower; product and closed-subspace compactness are
   lem-weil-pbc-tychonoff-product-quasi-compact and lem-weil-pbc-closed-in-quasi-compact.
   Its projection onto P is surjective, including where b = 0. By condition (3) of
   det-pe-stonean-projective it admits a continuous section, giving a = bq with q integral.
2. Select a maximal absolute-value entry by a finite clopen partition. For two continuous
   entries h,g, the closure C of {|h| < |g|} is clopen. On C, |h| ≤ |g|; on its complement,
   |g| ≤ |h|. Choose g on C and h elsewhere. Finite iteration selects a maximum entry and
   records its row and column on finitely many clopen pieces, also at ties and common zeros.
3. Induct on min(n,m). If it is zero there are no entries and identity changes suffice.
   Otherwise piecewise constant permutation matrices S,T move the selected entry h to the
   top left of A = SFT. Every entry of A has absolute value at most |h|.
4. Bounded division gives A_i1 = h q_i and A_1j = h t_j with continuous integral q_i,t_j.
   Set R = I - sum q_i e_i1 and C = I - sum t_j e_1j, with indices strictly past the first.
   Both sums square to zero, so replacing minus by plus gives continuous integral inverses.
   Then RAC has top-left entry h, zero remaining first row and column, and lower block B
   with entries A_ij - q_i A_1j. These identities also hold at zeros of h.
5. Diagonalize B inductively by L',U'. Then L = diag(1,L') R S and
   U = T C diag(1,U') give the required matrix with diagonal h followed by that of B.
   Inverse entries are continuous as finite sums of products of continuous integral entries.
   For empty P all identities are vacuous. Zero matrices and varying zero loci are covered
   because bounded division never prescribes division by zero.
-/
theorem exists_continuous_integral_diagonalization_of_extremallyDisconnected
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (P : Type v) [TopologicalSpace P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] [ExtremallyDisconnected P]
    (n m : ℕ) (F : P → Matrix (Fin n) (Fin m) E)
    (hF : ∀ (i : Fin n) (j : Fin m),
      @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ F p i j)) :
    ∃ (L : P → Matrix.GeneralLinearGroup (Fin n) (coefficientExtensionIntegers l E))
      (U : P → Matrix.GeneralLinearGroup (Fin m) (coefficientExtensionIntegers l E))
      (d : Fin (min n m) → P → E),
      (∀ (i j : Fin n), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((L p).val i j : E))) ∧
      (∀ (i j : Fin n), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((L p)⁻¹).val i j : E))) ∧
      (∀ (i j : Fin m), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ ((U p).val i j : E))) ∧
      (∀ (i j : Fin m), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace
        (fun p ↦ (((U p)⁻¹).val i j : E))) ∧
      (∀ k : Fin (min n m), @Continuous P E _
        (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace (d k)) ∧
      (∀ (p : P) (i : Fin n) (j : Fin m), i.val ≠ j.val →
        ((L p).val.map (fun x ↦ (x : E)) * F p *
          (U p).val.map (fun x ↦ (x : E))) i j = 0) ∧
      (∀ (p : P) (k : Fin (min n m)),
        ((L p).val.map (fun x ↦ (x : E)) * F p *
          (U p).val.map (fun x ↦ (x : E)))
          (k.castLE (Nat.min_le_left n m)) (k.castLE (Nat.min_le_right n m)) = d k p) := by
  let : NormedField E := spectralNorm.normedField (Padic l) E
  obtain ⟨L, U, hL, hLi, hU, hUi, hdiag⟩ :=
    offDiagonal_induction l E P n m F hF
  let D := fun p ↦ (L p).val.map (fun x ↦ (x : E)) * F p *
    (U p).val.map (fun x ↦ (x : E))
  have hD : ∀ i j, Continuous (fun p ↦ D p i j) :=
    continuous_entries_mul (continuous_entries_mul hL hF) hU
  exact ⟨L, U, fun k p ↦ D p (k.castLE (Nat.min_le_left n m))
    (k.castLE (Nat.min_le_right n m)), hL, hLi, hU, hUi,
    fun k ↦ hD _ _, hdiag, fun _ _ ↦ rfl⟩

end Padic
