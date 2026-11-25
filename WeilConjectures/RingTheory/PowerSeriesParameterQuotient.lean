/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import WeilConjectures.RingTheory.CohenRing
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.PowerSeriesQuotientVariables
import WeilConjectures.RingTheory.PowerSeriesFullCoordinatesField
import WeilConjectures.RingTheory.PowerSeriesFullCoordinatesCohen

/-!
# Quotients of power series rings by partial parameter systems

Quotienting a power series ring over a field or a Cohen ring by part of a regular system of
parameters leaves a power series ring in the remaining parameters.

## References

* [Stacks, Tag 07NM] (parts (2) and (4))
-/

@[expose] public section

universe u

namespace MvPowerSeries

private theorem quotient_parameters_of_coordinates
    (A : Type u) [CommRing A] (n : ℕ) (z y : List (MvPowerSeries (Fin n) A))
    (e : MvPowerSeries (Fin (z ++ y).length) A ≃ₐ[A] MvPowerSeries (Fin n) A)
    (he : ∀ i, e (X i) = (z ++ y).get i) :
    ∃ q : MvPowerSeries (Fin y.length) A ≃ₐ[A]
        (MvPowerSeries (Fin n) A ⧸ Ideal.span {a | a ∈ z}),
      IsLocalHom q.toRingHom ∧
        ∀ i : Fin y.length, q (X i) = Ideal.Quotient.mk _ (y.get i) := by
  classical
  let d := (z ++ y).length
  let r := z.length
  let I : Ideal (MvPowerSeries (Fin d) A) :=
    Ideal.span {x | ∃ j : Fin d, j.val < r ∧ x = X j}
  let J : Ideal (MvPowerSeries (Fin n) A) := Ideal.span {a | a ∈ z}
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {a | a ∈ z} =
      (Ideal.span {x | ∃ j : Fin d, j.val < r ∧ x = X j}).map e.toRingHom
    rw [Ideal.map_span]
    congr 1
    ext a
    constructor
    · intro ha
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
      let j : Fin d := ⟨i.val, by simp [d]; omega⟩
      refine ⟨X j, ⟨j, i.isLt, rfl⟩, ?_⟩
      change e (X j) = a
      rw [he]
      simpa [j, List.get_eq_getElem, List.getElem_append_left] using hi
    · rintro ⟨x, ⟨j, hj, rfl⟩, rfl⟩
      change e (X j) ∈ z
      rw [he]
      have hget : (z ++ y).get j = z.get ⟨j.val, hj⟩ := by
        simp only [List.get_eq_getElem]
        exact List.getElem_append_left hj
      rw [hget]
      exact List.get_mem _ _
  have hr : r ≤ d := by simp [r, d]
  obtain ⟨q₀, hq₀⟩ := quotient_first_variables_equiv A d r hr
  let v : Fin y.length ≃ {j : Fin d // r ≤ j.val} :=
    { toFun := fun i ↦ ⟨⟨r + i.val, by simp only [d, List.length_append]; omega⟩,
        by change r ≤ r + i.val; omega⟩
      invFun := fun j ↦ ⟨j.val.val - r, by have := j.val.isLt; simp [d, r] at *; omega⟩
      left_inv := by intro i; apply Fin.ext; simp
      right_inv := by intro j; apply Subtype.ext; apply Fin.ext; simp; omega }
  let q := (renameEquiv A v).trans
    (q₀.symm.trans (Ideal.quotientEquivAlg I J e hIJ))
  refine ⟨q, ?_, ?_⟩
  · exact isLocalHom_of_leftInverse q.symm.toRingHom q.symm_apply_apply
  · intro i
    have hqi : q₀.symm (X (v i)) = Ideal.Quotient.mk I (X (v i).val) := by
      apply q₀.injective
      rw [q₀.apply_symm_apply, hq₀]
      exact (killCompl_X (R := A)
        (e := Function.Embedding.subtype (fun j : Fin d ↦ r ≤ j.val)) (v i)).symm
    change Ideal.quotientEquivAlg I J e hIJ
      (q₀.symm (renameEquiv A v (X i))) = _
    have hrename : renameEquiv A v (X i) = X (v i) := rename_X v i
    rw [hrename, hqi, Ideal.quotientEquivAlg_mk, he]
    congr 1
    simp [v, r, List.get_eq_getElem, List.getElem_append_right]


/-- Quotienting field power series by the first part of a chosen regular parameter system
leaves power series with the remaining parameters as variables. -/
theorem exists_algEquiv_quotient_parameters_field
    (K : Type u) [Field K] (n : ℕ)
    (z y : List (MvPowerSeries (Fin n) K))
    (hparams : IsLocalRing.IsRegularSystemOfParameters (z ++ y)) :
    z.length ≤ n ∧ y.length = n - z.length ∧
      ∃ e : MvPowerSeries (Fin y.length) K ≃ₐ[K]
          (MvPowerSeries (Fin n) K ⧸ Ideal.span {a | a ∈ z}),
        IsLocalHom e.toRingHom ∧
          ∀ i : Fin y.length, e (X i) = Ideal.Quotient.mk _ (y.get i) := by
  have hdim : ringKrullDim (MvPowerSeries (Fin n) K) = (n : WithBot ℕ∞) := by
    obtain h | ⟨p, hp, _⟩ := power_series_field_cohen_regular_complete
      (Λ := K) n (Or.inl (Field.toIsField K))
    · obtain ⟨_, _, _, _, _, _, _, _, _, hd⟩ := h
      exact hd
    · obtain ⟨_, _, hdvr, _⟩ := hp
      let := hdvr
      exact False.elim (IsDiscreteValuationRing.not_isField K (Field.toIsField K))
  have hlen : (z ++ y).length = n := by
    have h := hparams.2.trans hdim
    exact_mod_cast h
  obtain ⟨e, he⟩ := exists_algEquiv_full_parameters_field K n (z ++ y) hparams hlen
  have hsum : z.length + y.length = n := by simpa using hlen
  refine ⟨by omega, by omega, ?_⟩
  exact quotient_parameters_of_coordinates K n z y e he

/-- In the Cohen case the coefficient uniformizer is retained, while quotienting by z
leaves power series in the remaining chosen parameters over the same Cohen ring. -/
theorem exists_algEquiv_quotient_parameters_cohen
    (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    (p n : ℕ) (hΛ : IsCohenRing p Λ)
    (z y : List (MvPowerSeries (Fin n) Λ))
    (hparams : IsLocalRing.IsRegularSystemOfParameters (C (p : Λ) :: (z ++ y))) :
    z.length ≤ n ∧ y.length = n - z.length ∧
      ∃ e : MvPowerSeries (Fin y.length) Λ ≃ₐ[Λ]
          (MvPowerSeries (Fin n) Λ ⧸ Ideal.span {a | a ∈ z}),
        IsLocalHom e.toRingHom ∧
          (∀ i : Fin y.length, e (X i) = Ideal.Quotient.mk _ (y.get i)) ∧
          e (C (p : Λ)) = Ideal.Quotient.mk _ (C (p : Λ)) := by
  have hdim : ringKrullDim (MvPowerSeries (Fin n) Λ) = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    obtain ⟨hf, _⟩ | ⟨p', hp', _, _, _, _, _, _, _, _, hd⟩ :=
      power_series_field_cohen_regular_complete (Λ := Λ) n (Or.inr ⟨p, hΛ⟩)
    · obtain ⟨_, _, hdvr, _⟩ := hΛ
      let := hdvr
      exact False.elim (IsDiscreteValuationRing.not_isField Λ hf)
    · exact hd
  have hlen : (z ++ y).length = n := by
    have h := hparams.2.trans hdim
    have h' : (C (p : Λ) :: (z ++ y)).length = n + 1 := by exact_mod_cast h
    simpa using h'
  obtain ⟨e, he⟩ := exists_algEquiv_full_parameters_cohen Λ p n hΛ (z ++ y) hparams hlen
  have hsum : z.length + y.length = n := by simpa using hlen
  obtain ⟨q, hq, hqy⟩ := quotient_parameters_of_coordinates Λ n z y e he
  refine ⟨by omega, by omega, q, hq, hqy, ?_⟩
  exact q.commutes (p : Λ)

end MvPowerSeries
