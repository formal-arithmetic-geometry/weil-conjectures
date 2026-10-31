/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.LinearAlgebra.Matrix.RowMinorIdealStableInvariance
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Row-minor ideals under arbitrary extension of scalars

Source: Stacks Project, More on Algebra, Tags 07Z8 and 07ZA, proof of (3)
(blueprint: lem-trf-row-minor-ideal-scalar-extension).

The existing `Matrix.rowMinorIdeal n (n - r)` gives the ideal of `r`-minors when
`r ≤ n`; for `r > n` the ideal is zero. The tensor factors use Mathlib's
base-change convention `A ⊗[R] M`. The coordinate identities explicitly commute
these factors to display the convention `M ⊗[R] A` in the source statement.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Matrix

-- Multilinearity extends membership from generating rows to their span.
private theorem multilinear_mem_span {B M : Type*} [CommRing B]
    [AddCommGroup M] [Module B M] {ι : Type*} [Finite ι]
    (f : MultilinearMap B (fun _ : ι ↦ M) B) (t : Set M) (I : Ideal B)
    (h : ∀ m : ι → M, (∀ i, m i ∈ t) → f m ∈ I)
    (m : ι → M) (hm : ∀ i, m i ∈ Submodule.span B t) : f m ∈ I := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have aux : ∀ s : Finset ι, ∀ m : ι → M,
      (∀ i ∈ s, m i ∈ Submodule.span B t) →
      (∀ i ∉ s, m i ∈ t) → f m ∈ I := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro m _ ht; exact h m (fun i ↦ ht i (by simp))
    | @insert i s hi ih =>
      intro m hs ht
      have hm := hs i (by simp)
      have step : ∀ x ∈ Submodule.span B t, f (Function.update m i x) ∈ I := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          apply ih
          · intro j hj
            simpa [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)] using
              hs j (by simp [hj])
          · intro j hj
            by_cases hji : j = i
            · subst j; simpa using hx
            · simpa [Function.update_of_ne hji] using ht j (by simp [hj, hji])
        | zero => simpa only [f.map_update_zero] using I.zero_mem
        | add x y _ _ hx hy =>
          simpa only [f.map_update_add] using I.add_mem hx hy
        | smul a x _ hx =>
          simpa only [f.map_update_smul] using I.smul_mem a hx
      simpa using step (m i) hm
  exact aux Finset.univ m (fun i _ ↦ hm i) (by simp)

private theorem row_det_mem {B : Type*} [CommRing B] {n k : ℕ}
    (hk : k < n) (K : Submodule B (Fin n → B))
    (D : Matrix (Fin (n - k)) (Fin n) B) (hD : ∀ i, D i ∈ K)
    (T : {T : Finset (Fin n) // T.card = n - k}) :
    (D.submatrix id (T.val.orderEmbOfFin T.property)).det ∈ rowMinorIdeal n k K := by
  classical
  rw [rowMinorIdeal, if_neg (by omega)]
  have hle : minorIdeal (n - k) n (n - k) D ≤
      ⨆ (E : Matrix (Fin (n - k)) (Fin n) B) (_ : ∀ i, E i ∈ K),
        minorIdeal (n - k) n (n - k) E :=
    le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  apply hle
  apply Ideal.subset_span
  refine ⟨(⟨Finset.univ, by simp⟩, T), ?_⟩
  have he : ((Finset.univ : Finset (Fin (n - k))).orderEmbOfFin (by simp) :
      Fin (n - k) → Fin (n - k)) = id :=
    (Finset.orderEmbOfFin_unique (by simp) (fun _ ↦ Finset.mem_univ _)
      (fun _ _ h ↦ h)).symm
  simp [he]

private theorem row_ideal_map {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (n k : ℕ)
    (K : Submodule R (Fin n → R)) :
    rowMinorIdeal n k (Submodule.span A (Set.range (fun z : K ↦
      fun j : Fin n ↦ algebraMap R A (z.val j)))) =
      Ideal.map (algebraMap R A) (rowMinorIdeal n k K) := by
  classical
  let φ := algebraMap R A
  let t : Set (Fin n → A) := Set.range (fun z : K ↦ fun j ↦ φ (z.val j))
  by_cases hk : n ≤ k
  · simp [rowMinorIdeal, hk, Ideal.map_top]
  have hkn : k < n := by omega
  apply le_antisymm
  · rw [rowMinorIdeal, if_neg hk]
    refine iSup_le fun D ↦ iSup_le fun hD ↦ Ideal.span_le.mpr ?_
    rintro _ ⟨⟨S, T⟩, rfl⟩
    let c := T.val.orderEmbOfFin T.property
    let f : MultilinearMap A (fun _ : Fin (n - k) ↦ Fin n → A) A :=
      (detRowAlternating : (Fin (n - k) → A) [⋀^Fin (n - k)]→ₗ[A] A).toMultilinearMap
        |>.compLinearMap (fun _ ↦ {
          toFun := fun x j ↦ x (c j)
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl })
    change f (fun i ↦ D (S.val.orderEmbOfFin S.property i)) ∈ _
    apply multilinear_mem_span f t _
    · intro m hm
      choose z hz using hm
      let E : Matrix (Fin (n - k)) (Fin n) R := fun i ↦ (z i).val
      have he : f m = φ ((E.submatrix id c).det) := by
        rw [RingHom.map_det]
        change Matrix.det (fun i j ↦ m i (c j)) =
          Matrix.det (fun i j ↦ φ ((z i).val (c j)))
        apply congrArg Matrix.det
        funext i j
        exact congrFun (hz i).symm (c j)
      rw [he]
      exact Ideal.mem_map_of_mem φ (row_det_mem hkn K E (fun i ↦ (z i).property) T)
    · intro i
      exact hD _
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [rowMinorIdeal, if_neg hk]
    refine iSup_le fun D ↦ iSup_le fun hD ↦ Ideal.span_le.mpr ?_
    rintro _ ⟨⟨S, T⟩, rfl⟩
    change φ ((D.submatrix (S.val.orderEmbOfFin S.property)
      (T.val.orderEmbOfFin T.property)).det) ∈ rowMinorIdeal n k (Submodule.span A t)
    rw [RingHom.map_det]
    let E : Matrix (Fin (n - k)) (Fin n) A :=
      fun i j ↦ φ (D (S.val.orderEmbOfFin S.property i) j)
    exact row_det_mem hkn (Submodule.span A t) E
      (fun i ↦ Submodule.subset_span ⟨⟨_, hD _⟩, rfl⟩) T

/-- Scalar extension preserves the ideal generated by minors of arbitrary relation rows,
with the finite-free tensor coordinate isomorphism and its image on the relation submodule.
Source: Stacks Project, More on Algebra, Tag 07ZA, proof of (3), and the kernel-row
interpretation in Tag 07Z8 (blueprint: lem-trf-row-minor-ideal-scalar-extension).

Proof:
1. Use `TensorProduct.piScalarRight` for the finite-free coordinate isomorphism.
Its pure-tensor formula gives the forward coordinates. Decompose a coordinate
vector into single-coordinate vectors; linearity and the inverse formula on
such vectors give the displayed sum, also for `n = 0`.
2. `Submodule.baseChange_eq_span` identifies the image of the tensored inclusion
with the span of `1 ⊗ z`. Transporting this span by the coordinate map gives
exactly the asserted span of coordinatewise images. No injectivity is used.
3. Prove the ideal equality first for arbitrary `rowMinorIdeal n k`. If `n ≤ k`,
both sides are the unit ideal. Otherwise determinants commute with the algebra
map by `RingHom.map_det`, giving the inclusion of the mapped ideal into the new
row-minor ideal.
4. For the reverse inclusion fix the selected columns. Their determinant is a
multilinear function of the rows. Membership of its value in an ideal extends
from tuples of generating rows to tuples of rows in their span: induct on the
finite set of rows allowed in the span, using `Submodule.span_induction` in each
inserted row. Zero rows give zero, sums give sums, and scalar multiples give
scalar multiples. For a tuple of generating image rows, `RingHom.map_det`
identifies its determinant with the image of an original minor, which belongs
to the mapped ideal. This proves the reverse inclusion.
5. Substitute `k = n - r` when `r ≤ n`. When `r > n`, both displayed ideals
are zero. Neither flatness nor finite generation of `K` is assumed.
-/
theorem rowMinorIdeal_scalar_extension {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (n r : ℕ)
    (K : Submodule R (Fin n → R)) :
    ∃ θ : (A ⊗[R] (Fin n → R)) ≃ₗ[A] (Fin n → A),
      (∀ (x : Fin n → R) (a : A),
        θ (TensorProduct.comm R (Fin n → R) A (x ⊗ₜ[R] a)) =
          fun j : Fin n ↦ a * algebraMap R A (x j)) ∧
      (∀ a : Fin n → A,
        TensorProduct.comm R A (Fin n → R) (θ.symm a) =
          ∑ j : Fin n, (Pi.single j 1 : Fin n → R) ⊗ₜ[R] a j) ∧
      (Submodule.map θ.toLinearMap (LinearMap.range (K.subtype.baseChange A)) =
        Submodule.span A (Set.range (fun z : K ↦
          fun j : Fin n ↦ algebraMap R A (z.val j)))) ∧
      (if n < r then (⊥ : Ideal A) else
        rowMinorIdeal n (n - r) (Submodule.span A (Set.range (fun z : K ↦
          fun j : Fin n ↦ algebraMap R A (z.val j))))) =
        Ideal.map (algebraMap R A)
          (if n < r then (⊥ : Ideal R) else rowMinorIdeal n (n - r) K) := by
  classical
  let θ := TensorProduct.piScalarRight R A A (Fin n)
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  · intro x a
    ext j
    simp [θ, Algebra.smul_def, mul_comm]
  · intro a
    have ha : a = ∑ j : Fin n, Pi.single j (a j) := by
      ext j
      simp
    conv_lhs => rw [ha]
    simp only [map_sum, TensorProduct.piScalarRight_symm_single, θ,
      TensorProduct.comm_tmul]
  · change Submodule.map θ.toLinearMap (K.baseChange A) = _
    rw [Submodule.baseChange_eq_span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      ext j
      simp [θ, Algebra.smul_def]
    · rintro ⟨z, rfl⟩
      refine ⟨1 ⊗ₜ[R] z.val, ⟨z.val, z.property, rfl⟩, ?_⟩
      ext j
      simp [θ, Algebra.smul_def]
  · by_cases h : n < r
    · simp [h]
    · simpa only [if_neg h] using row_ideal_map n (n - r) K

end Matrix
