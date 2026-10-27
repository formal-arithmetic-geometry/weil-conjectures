module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span

import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Saturation of linear chart relations from Koszul syzygies

Source: Stacks Project, More on Algebra, Tag 0BIQ (lemma-blowup-regular-sequence),
the final inference from vanishing first Koszul homology to torsion-freeness,
written in degree-one syzygy coordinates.
(blueprint: lem-trf-koszul-relations-quotient-torsionfree)
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace RingTheory

/-- If every relation on a nonempty tuple is a Koszul boundary, its linear chart
relation quotient has no torsion under the first entry. Here the tuple length is
`n + 1`, its first entry is `f 0`, and the remaining entries are `f i.succ`.
The standard unit vectors of the free tuple module are `Pi.single i 1`.

Source: Stacks Project, More on Algebra, Tag 0BIQ (lemma-blowup-regular-sequence),
the final H₁-to-torsion-free inference in explicit coordinates.
(blueprint: lem-trf-koszul-relations-quotient-torsionfree)

Proof plan:
1. Write `g_i = f 0 * t i - f i.succ` and `J = Ideal.span (Set.range g)`.
   If `f 0 * h = ∑ i, c_i * g_i`, the vector with first coordinate
   `h - ∑ i, c_i * t i` and remaining coordinates `c_i` is a relation on `f`.
   Apply the hypothesis to express it as a sum of Koszul generators. This uses
   the free tuple module of `def-weil-pbc-free-module`.
2. Apply the linear functional `λ(w) = w 0 + ∑ i, t i * w i.succ`.
   Its value on that vector is `h`. Its value on `f 0 • e_j - f j • e_0`
   is `g_j`; its value on `f_i • e_j - f_j • e_i`, with both indices positive,
   is `t_i * g_j - t_j * g_i`. Hence every summand maps into `J`, so `h ∈ J`.
   For `n = 0`, the sums are empty and the same hypothesis gives `h = 0`.
3. Represent quotient classes by elements of the ring. Step 2 gives zero kernel
   for multiplication by the image of `f 0`; applying it to a difference gives
   injectivity. Induction on `N` gives vanishing of every class killed by its
   `N`th power. Since the quotient map preserves products and powers, this is
   equivalent to `f 0 ^ N * h ∈ J → h ∈ J`.
-/
theorem koszul_relations_quotient_torsionfree
    {S : Type u} [CommRing S] (n : ℕ) (f : Fin (n + 1) → S) (t : Fin n → S)
    (hsyzygies : ∀ v : Fin (n + 1) → S, (∑ i, f i * v i) = 0 →
      ∃ b : Fin (n + 1) → Fin (n + 1) → S,
        v = ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j),
          b i j • (f i • Pi.single j (1 : S) - f j • Pi.single i (1 : S))) :
    Function.Injective
        (fun x : S ⧸ Ideal.span (Set.range (fun i : Fin n ↦ f 0 * t i - f i.succ)) ↦
          Ideal.Quotient.mk _ (f 0) * x) ∧
      (∀ (h : S) (N : ℕ),
        f 0 ^ N * h ∈ Ideal.span (Set.range (fun i : Fin n ↦ f 0 * t i - f i.succ)) →
          h ∈ Ideal.span (Set.range (fun i : Fin n ↦ f 0 * t i - f i.succ))) ∧
      (∀ (N : ℕ)
        (x : S ⧸ Ideal.span (Set.range (fun i : Fin n ↦ f 0 * t i - f i.succ))),
        Ideal.Quotient.mk _ (f 0) ^ N * x = 0 → x = 0) := by
  classical
  let J : Ideal S := Ideal.span (Set.range (fun i : Fin n ↦ f 0 * t i - f i.succ))
  let q := Ideal.Quotient.mk J
  let w : Fin (n + 1) → S := Fin.cons 1 t
  let L : (Fin (n + 1) → S) →ₗ[S] S :=
    { toFun := fun v ↦ ∑ i, w i * v i
      map_add' := by
        intro x y
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  have hsingle (i : Fin (n + 1)) : L (Pi.single i (1 : S)) = w i := by
    simp [L, Pi.single_apply, mul_ite]
  have hf (i : Fin (n + 1)) : q (f i) = q (f 0) * q (w i) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [w, q]
    · have hg : f 0 * t j - f j.succ ∈ J := Ideal.subset_span ⟨j, rfl⟩
      have he := (Ideal.Quotient.eq_zero_iff_mem).2 hg
      change q (f j.succ) = q (f 0) * q (t j)
      exact (sub_eq_zero.mp (by simpa only [map_sub, map_mul] using he)).symm
  have hboundary (i j : Fin (n + 1)) :
      L (f i • Pi.single j (1 : S) - f j • Pi.single i (1 : S)) ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (L (f i • Pi.single j (1 : S) - f j • Pi.single i (1 : S))) = 0
    rw [map_sub, map_smul, map_smul, hsingle, hsingle]
    simp only [smul_eq_mul, map_sub, map_mul]
    rw [hf i, hf j]
    ring
  have hsaturate (h : S) (hh : f 0 * h ∈ J) : h ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hh
    let v : Fin (n + 1) → S := Fin.cons (h - ∑ i, c i * t i) c
    have hv : (∑ i, f i * v i) = 0 := by
      rw [Fin.sum_univ_succ]
      simp only [v, Fin.cons_zero, Fin.cons_succ]
      have hexpand :
          (∑ i, c i * (f 0 * t i - f i.succ)) =
            f 0 * (∑ i, c i * t i) - ∑ i, f i.succ * c i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hexpand] at hc
      rw [mul_sub]
      linear_combination -hc
    obtain ⟨b, hb⟩ := hsyzygies v hv
    have hLv : L v = h := by
      dsimp [L]
      rw [Fin.sum_univ_succ]
      simp only [w, v, Fin.cons_zero, Fin.cons_succ, one_mul]
      have hcomm : (∑ i, t i * c i) = ∑ i, c i * t i := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      rw [hcomm]
      ring
    rw [← hLv, hb, map_sum]
    apply J.sum_mem
    intro i _
    rw [map_sum]
    apply J.sum_mem
    intro j _
    rw [map_smul]
    exact J.smul_mem (b i j) (hboundary i j)
  have hzero (x : S ⧸ J) (hx : q (f 0) * x = 0) : x = 0 := by
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsaturate
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using hx
  have hinjective : Function.Injective (fun x : S ⧸ J ↦ q (f 0) * x) := by
    intro x y hxy
    change q (f 0) * x = q (f 0) * y at hxy
    have h := hzero (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp h
  have hpower (N : ℕ) (x : S ⧸ J) (hx : q (f 0) ^ N * x = 0) : x = 0 := by
    induction N with
    | zero => simpa using hx
    | succ N ih =>
      apply ih
      apply hzero
      simpa only [pow_succ', mul_assoc] using hx
  refine ⟨hinjective, ?_, hpower⟩
  intro h N hh
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hpower N
  have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  simpa only [map_mul, map_pow] using hz

end RingTheory
