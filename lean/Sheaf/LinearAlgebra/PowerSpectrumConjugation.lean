module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse

/-!
# Algebraic multiplicities and reality for powers of endomorphisms

Source: Weil conjectures blueprint, `sec-deligne-laumon-general/sk-i-dl-general-real`,
`thm-zl-real-mixed-by-curves.proof.md`, paragraph 1, final sentences
(blueprint: lem-zl-power-spectrum-conjugation).
-/

@[expose] public section

universe u v

open Polynomial

namespace LinearMap

/-- Positive powers raise each characteristic root to that power, keeping every occurrence.
Both determinant products hold, and the root multiplicity counts all occurrences that collide.
Conjugation stability of the complex root multiset is preserved, and the mapped reverse
characteristic polynomial comes from a real polynomial.

Source: Weil conjectures blueprint, `sec-deligne-laumon-general/sk-i-dl-general-real`,
`thm-zl-real-mixed-by-curves.proof.md`, paragraph 1, final sentences
(blueprint: lem-zl-power-spectrum-conjugation).

Proof plan:
1. Use `p-linear-triangular` to obtain a complete invariant flag over the algebraically
   closed field. Choose an adapted basis and reverse it to make the matrix lower triangular.
2. Apply `lem-weil-pbc-block-triangular-determinant` inductively, including the empty
   determinant, to compute the characteristic polynomial as the product of its diagonal
   factors. Group equal diagonal values; the remaining factors evaluate nontrivially there,
   so their multiplicities identify the diagonal multiset with the given root enumeration.
3. Products of lower triangular matrices are lower triangular, and their diagonal entries
   multiply. Thus the diagonal of the nth power consists of the nth powers of the original
   diagonal entries. Apply the same determinant calculation to both `T I - A^n` and
   `I - T A^n` to obtain the two products, without any invertibility or semisimplicity.
4. Group factors with the same powered value. The other factors evaluate nontrivially,
   so root multiplicity is exactly the number of occurrences with that powered value.
   This also applies when the characteristic divides n.
5. Conjugation invariance provides a permutation of the occurrences. Conjugation and the
   field isomorphism preserve powers, so the same permutation works for the powered list.
   Conjugating the reverse product fixes it coefficientwise; each coefficient is therefore
   real. Empty lists give products 1, and a zero eigenvalue gives a reverse factor 1.
-/
theorem power_spectrum_conjugation
    {K : Type u} [Field K] [IsAlgClosed K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A : V →ₗ[K] V) (n : ℕ) (hn : 1 ≤ n)
    (α : Fin (Module.finrank K V) → K)
    (hα : A.charpoly.roots = Finset.univ.val.map α) :
    (A ^ n).charpoly = ∏ j, (X - C (α j ^ n)) ∧
    (A ^ n).charpolyRev = ∏ j, (1 - X * C (α j ^ n)) ∧
    (∀ β : K, rootMultiplicity β (A ^ n).charpoly =
      Nat.card {j : Fin (Module.finrank K V) // α j ^ n = β}) ∧
    (∀ ι : K ≃+* ℂ,
      Finset.univ.val.map (fun j ↦ star (ι (α j))) =
        Finset.univ.val.map (fun j ↦ ι (α j)) →
      Finset.univ.val.map (fun j ↦ star (ι (α j ^ n))) =
        Finset.univ.val.map (fun j ↦ ι (α j ^ n)) ∧
      ∃ P : ℝ[X], P.map Complex.ofRealHom = (A ^ n).charpolyRev.map ι.toRingHom) := by
  classical
  by_cases hzero : n = 0
  · subst n
    exact False.elim (Nat.not_succ_le_zero 0 hn)
  obtain ⟨b, hb⟩ := Module.End.exists_basis_isUpperTriangular_toMatrix A
  let B := toMatrix b b A
  have hB : B.BlockTriangular (fun i ↦ i) := hb
  have hdiag : ∀ k (i : Fin (Module.finrank K V)), (B ^ k) i i = B i i ^ k := by
    intro k
    induction k with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [pow_succ, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ih, pow_succ]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · rw [(hB.pow k) hlt]; simp
        · rw [hB hgt]; simp
      · simp
  have hχ : A.charpoly = ∏ j, (X - C (B j j)) := by
    rw [← charpoly_toMatrix A b]
    exact Matrix.charpoly_of_isUpperTriangular B hb
  have hroots : Finset.univ.val.map (fun j ↦ B j j) = Finset.univ.val.map α := by
    rw [← hα, hχ]
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using
      (roots_multiset_prod_X_sub_C (Finset.univ.val.map (fun j ↦ B j j))).symm
  have hχn : (A ^ n).charpoly = ∏ j, (X - C (α j ^ n)) := by
    rw [← charpoly_toMatrix (A ^ n) b, ← toMatrix_pow,
      Matrix.charpoly_of_isUpperTriangular _ (hB.pow n)]
    simp_rw [hdiag]
    have h := congrArg (fun s : Multiset K ↦
      (s.map (fun a ↦ X - C (a ^ n))).prod) hroots
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using h
  have hrev : (A ^ n).charpolyRev = ∏ j, (1 - X * C (α j ^ n)) := by
    rw [charpolyRev_def, hχn]
    simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val, mul_comm] using
      reverse_multiset_prod_X_sub_C (Finset.univ.val.map (fun j ↦ α j ^ n))
  refine ⟨hχn, hrev, ?_, ?_⟩
  · intro β
    rw [← count_roots, hχn]
    have hr : (∏ j, (X - C (α j ^ n))).roots =
        Finset.univ.val.map (fun j ↦ α j ^ n) := by
      simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using
        roots_multiset_prod_X_sub_C (Finset.univ.val.map (fun j ↦ α j ^ n))
    rw [hr, Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [eq_comm, ← Finset.filter_val]
    rfl
  · intro ι hc
    have hcn : Finset.univ.val.map (fun j ↦ star (ι (α j ^ n))) =
        Finset.univ.val.map (fun j ↦ ι (α j ^ n)) := by
      have h := congrArg (Multiset.map (fun z : ℂ ↦ z ^ n)) hc
      simpa only [Multiset.map_map, Function.comp_def, map_pow, star_pow] using h
    refine ⟨hcn, ?_⟩
    let Q := (A ^ n).charpolyRev.map ι.toRingHom
    have hQprod : Q = ∏ j, (1 - X * C (ι (α j ^ n))) := by
      simp only [Q, hrev, Polynomial.map_prod, Polynomial.map_sub,
        Polynomial.map_one, Polynomial.map_mul, map_X, map_C]
      rfl
    have hQ : Q.map (starRingEnd ℂ) = Q := by
      have h := congrArg (fun s : Multiset ℂ ↦
        (s.map (fun z ↦ 1 - X * C z)).prod) hcn
      rw [hQprod, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
        map_X, map_C, starRingEnd_apply]
      simpa only [Multiset.map_map, Function.comp_def, Finset.prod_map_val] using h
    let P : ℝ[X] := .ofFinsupp (.ofCoeff (Finsupp.mapRange Complex.re (by simp) Q.toFinsupp.coeff))
    refine ⟨P, ?_⟩
    ext k
    have hk := congrArg (fun p : ℂ[X] ↦ p.coeff k) hQ
    have hr : ((Q.coeff k).re : ℂ) = Q.coeff k :=
      Complex.conj_eq_iff_re.mp (by simpa using hk)
    change (P.map Complex.ofRealHom).coeff k = Q.coeff k
    calc
      (P.map Complex.ofRealHom).coeff k = Complex.ofRealHom (Q.coeff k).re := by
        rw [Polynomial.coeff_map]
        rfl
      _ = Q.coeff k := hr

end LinearMap
