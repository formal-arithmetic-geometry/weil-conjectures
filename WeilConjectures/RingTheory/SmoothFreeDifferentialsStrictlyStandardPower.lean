/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.RingTheory.StrictlyStandardElement
import WeilConjectures.LinearAlgebra.Matrix.LeftInverseMinors
import WeilConjectures.RingTheory.PresentationLocalizedConormalSplit
import WeilConjectures.RingTheory.SmoothStableConormalBasis
import WeilConjectures.RingTheory.LocalizedConormalBasisJacobian

/-!
# Powers of an element with smooth free localization are strictly standard

We show that if `A_a` is smooth over `R` with stably free module of Kähler differentials,
then all sufficiently large powers of `a` are strictly standard in `A` over `R`.

## Main statements

* `smooth_free_differentials_strictly_standard_power`.

## References

* [Stacks, Tag 07EZ]
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

private theorem common_denominator {A : Type v} [CommRing A] (a : A)
    {ι : Type*} [Finite ι] (f : ι → Localization.Away a) :
    ∃ (k : ℕ) (g : ι → A), ∀ i,
      algebraMap A (Localization.Away a) (g i) =
        f i * algebraMap A (Localization.Away a) a ^ k := by
  classical
  let _ := Fintype.ofFinite ι
  choose k g hg using fun i ↦ IsLocalization.Away.surj a (f i)
  let K := Finset.univ.sup k
  refine ⟨K, fun i ↦ g i * a ^ (K - k i), ?_⟩
  intro i
  have hi : k i ≤ K := Finset.le_sup (Finset.mem_univ i)
  rw [map_mul, map_pow, ← hg i, mul_assoc, ← pow_add, Nat.add_sub_of_le hi]

private theorem clear_matrix_left_inverse {A : Type v} [CommRing A] (a : A)
    {n c : ℕ} (D : Matrix (Fin n) (Fin c) A)
    (L : Matrix (Fin c) (Fin n) (Localization.Away a))
    (hL : L * D.map (algebraMap A (Localization.Away a)) = 1) :
    ∃ (k : ℕ) (B : Matrix (Fin c) (Fin n) A), B * D = a ^ k • 1 := by
  classical
  let φ := algebraMap A (Localization.Away a)
  obtain ⟨u, g, hg⟩ := common_denominator a (fun ij : Fin c × Fin n ↦ L ij.1 ij.2)
  let B₀ : Matrix (Fin c) (Fin n) A := fun i j ↦ g (i, j)
  have hB₀ : B₀.map φ = φ a ^ u • L := by
    ext i j
    simpa [B₀, φ, mul_comm] using hg (i, j)
  have hmap : (B₀ * D).map φ = (a ^ u • (1 : Matrix (Fin c) (Fin c) A)).map φ := by
    rw [Matrix.map_mul, hB₀, Matrix.smul_mul, hL]
    ext i j
    by_cases hij : i = j <;> simp [φ, smul_eq_mul, hij]
  have heq (ij : Fin c × Fin c) :
      ∃ v : ℕ, a ^ v * (B₀ * D) ij.1 ij.2 =
        a ^ v * (a ^ u • (1 : Matrix (Fin c) (Fin c) A)) ij.1 ij.2 :=
    IsLocalization.Away.exists_of_eq a (congrFun (congrFun hmap ij.1) ij.2)
  choose v hv using heq
  let V := Finset.univ.sup v
  have hclear : a ^ V • (B₀ * D) = a ^ (V + u) • (1 : Matrix (Fin c) (Fin c) A) := by
    ext i j
    have hij : v (i, j) ≤ V := Finset.le_sup (Finset.mem_univ (i, j))
    have h := congrArg (fun z ↦ a ^ (V - v (i, j)) * z) (hv (i, j))
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc] at h ⊢
    rw [← pow_add, Nat.sub_add_cancel hij] at h
    simpa only [pow_add, mul_assoc] using h
  exact ⟨V + u, a ^ V • B₀, by rw [Matrix.smul_mul, hclear]⟩

/-- If the localization at `a` is smooth and its module of Kähler differentials is
stably free, then all sufficiently large powers of `a` are strictly standard. -/
theorem smooth_free_differentials_strictly_standard_power
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    [FinitePresentation R A] (a : A)
    [Algebra.Smooth R (Localization.Away a)]
    (s t : ℕ)
    (hstable : Nonempty
      ((KaehlerDifferential R (Localization.Away a) × (Fin s →₀ Localization.Away a))
        ≃ₗ[Localization.Away a] (Fin t →₀ Localization.Away a))) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ ∀ e : ℕ, e₀ ≤ e →
      IsStrictlyStandardElement (R := R) (a ^ e) := by
  classical
  obtain ⟨n₀, m₀, ⟨P₀⟩⟩ := Presentation.exists_presentation_fin R A
  let S := Localization.Away a
  let M := S ⊗[A] P₀.toExtension.Cotangent
  obtain ⟨ec⟩ := P₀.localized_conormal_equiv a
  obtain ⟨eΩ⟩ := hstable
  let eΩ' : (KaehlerDifferential R S × (Fin s → S)) ≃ₗ[S] (Fin t → S) :=
    ((LinearEquiv.refl S _).prodCongr
      (Finsupp.linearEquivFunOnFinite S S (Fin s)).symm).trans
      (eΩ.trans (Finsupp.linearEquivFunOnFinite S S (Fin t)))
  let esum : ((Fin n₀ → S) × (Fin s → S)) ≃ₗ[S] (Fin (n₀ + s) → S) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n₀) (Fin s) S S).symm.trans
      (LinearEquiv.piCongrLeft S (fun _ ↦ S) finSumFinEquiv)
  let eM : (M × (Fin t → S)) ≃ₗ[S] (Fin (n₀ + s) → S) :=
    ((LinearEquiv.refl S M).prodCongr eΩ'.symm).trans
      ((LinearEquiv.prodAssoc S M (KaehlerDifferential R S) (Fin s → S)).symm.trans
        ((ec.prodCongr (LinearEquiv.refl S _)).trans esum))
  obtain ⟨n, m, c, P, hc, b, hb⟩ :=
    exists_presentation_localized_conormal_basis R A a P₀ t (n₀ + s) ⟨eM⟩
  obtain ⟨hrel, L, hL⟩ := P.localized_conormal_basis_jacobian hc a b hb
  let J : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
      (Ideal.span (Set.range P.relation)) ^ 2
  have hrelpow (j : Fin m) : ∃ k : ℕ, ∀ e : ℕ, k ≤ e → c ≤ j.val →
      P.σ (a ^ e) * P.relation j ∈ J := by
    by_cases hj : c ≤ j.val
    · obtain ⟨z, hz, hmem⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff
          (Submonoid.powers (P.σ a)) (Localization.Away (P.σ a)) J
          (P.relation j)).mp (hrel j hj)
      obtain ⟨k, rfl⟩ := hz
      refine ⟨k, fun e he _ ↦ ?_⟩
      have hpow : (P.σ a) ^ e * P.relation j ∈ J := by
        have h := J.mul_mem_left ((P.σ a) ^ (e - k)) hmem
        simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel he] using h
      have hdiff : P.σ (a ^ e) - (P.σ a) ^ e ∈ P.ker := by
        rw [P.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub, map_pow]
        simp only [P.aeval_val_σ, sub_self]
      have hsq : (P.σ (a ^ e) - (P.σ a) ^ e) * P.relation j ∈ J := by
        apply Ideal.mem_sup_right
        rw [← P.span_range_relation_eq_ker] at hdiff
        rw [pow_two]
        exact Ideal.mul_mem_mul hdiff (Ideal.subset_span ⟨j, rfl⟩)
      have h := J.add_mem hsq hpow
      simpa only [sub_mul, sub_add_cancel] using h
    · exact ⟨0, fun _ _ hj' ↦ (hj hj').elim⟩
  choose k hk using hrelpow
  let e₁ := Finset.univ.sup k
  let D : Matrix (Fin n) (Fin c) A := fun i j ↦
    MvPolynomial.aeval P.val (MvPolynomial.pderiv i
      (P.relation (Fin.castLE (le_trans hc (min_le_right n m)) j)))
  obtain ⟨e₂, B, hB⟩ := clear_matrix_left_inverse a D L hL
  have hminor := (Matrix.scalar_left_inverse_maximal_minors n c
    (le_trans hc (min_le_left n m)) D).2 (a ^ e₂) B hB
  let e₀ := max 1 (max e₁ (e₂ * c))
  refine ⟨e₀, le_max_left _ _, fun e he ↦ ?_⟩
  have he₁ : e₁ ≤ e := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) he
  have he₂ : e₂ * c ≤ e := le_trans
    (le_trans (le_max_right _ _) (le_max_right _ _)) he
  refine ⟨n, m, c, P, hc,
    fun I ↦ a ^ (e - e₂ * c) *
      (B.submatrix (fun i ↦ i) (I.val.orderEmbOfFin I.property)).det, ?_, ?_⟩
  · have hp : a ^ e = a ^ (e - e₂ * c) * (a ^ e₂) ^ c := by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel he₂]
    rw [hp, hminor.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    rw [mul_assoc]
    apply congrArg (fun z ↦ a ^ (e - e₂ * c) * z)
    apply congrArg (fun z ↦
      (B.submatrix (fun i ↦ i) (I.val.orderEmbOfFin I.property)).det * z)
    exact (Matrix.det_transpose
      (D.submatrix (I.val.orderEmbOfFin I.property) (fun j ↦ j))).symm
  · intro j hj
    exact hk j e (le_trans (Finset.le_sup (Finset.mem_univ j)) he₁) hj

end Algebra
