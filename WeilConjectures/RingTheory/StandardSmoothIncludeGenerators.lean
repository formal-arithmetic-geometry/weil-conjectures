/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Standard smooth presentations containing prescribed generators

A standard smooth algebra has a standard smooth presentation whose first variables map to
any prescribed finite family of elements.

## References

* [Stacks, Tag 07EY]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A standard smooth algebra has a standard smooth presentation (a Mathlib
`SubmersivePresentation` on the variables `Fin (n + m)` with relations `Fin c`, whose
Jacobian variables are the first `c`, `P.map = Fin.castLE hc`) whose first `n` variables
map to any prescribed finite family, repetitions allowed. Thus
`R[x_1, …, x_{n+m}]/(f_1, …, f_c) ≃ₐ[R] A` with `x_i ↦ P.val i`, and the image of
`det (∂f_j/∂x_i)_{i,j ≤ c}` is a unit of `A`. -/
theorem exists_standardSmoothPresentation_include_generators
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [IsStandardSmooth R A] (n : ℕ) (a : Fin n → A) :
    ∃ (m c : ℕ) (hc : c ≤ n + m) (P : SubmersivePresentation R A (Fin (n + m)) (Fin c)),
      n ≤ c ∧ P.map = Fin.castLE hc ∧ ∀ i : Fin n, P.val (Fin.castAdd m i) = a i := by
  classical
  obtain ⟨ι, σ, _, _, ⟨P₀⟩⟩ := ‹IsStandardSmooth R A›.out
  let _ := Fintype.ofFinite ι
  let _ := Fintype.ofFinite σ
  -- Present A over itself with the prescribed values and linear relations.
  let Q₁ : PreSubmersivePresentation A A (Fin n) (Fin n) := {
    val := a
    σ' := MvPolynomial.C
    aeval_val_σ' := by intro x; simp
    relation := fun i ↦ MvPolynomial.X i - MvPolynomial.C (a i)
    span_range_relation_eq_ker := by
      rw [Generators.ker_eq_ker_aeval_val]
      exact (MvPolynomial.ker_eval a).symm
    map := fun i ↦ i
    map_inj := Function.injective_id }
  have hQ : Q₁.jacobiMatrix = 1 := by
    ext i j : 1
    simp [Q₁, PreSubmersivePresentation.jacobiMatrix_apply, MvPolynomial.pderiv_X,
      Matrix.one_apply, Pi.single_apply, eq_comm]
  let Q : SubmersivePresentation A A (Fin n) (Fin n) := {
    toPreSubmersivePresentation := Q₁
    jacobian_isUnit := by
      rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, hQ,
        Matrix.det_one, map_one]
      exact isUnit_one }
  -- Composition supplies both the kernel calculation and the unit Jacobian.
  let P := Q.comp P₀
  -- Order the old Jacobian variables first, then their complement.
  let κ := ↥(Set.range P₀.map)ᶜ
  let d := Fintype.card σ
  let k := Fintype.card κ
  let es : Fin d ≃ σ := (Fintype.equivFin σ).symm
  let ek : Fin k ≃ κ := (Fintype.equivFin κ).symm
  let e₀ : Fin (d + k) ≃ ι :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr
      (es.trans (Equiv.ofInjective P₀.map P₀.map_inj)) ek).trans
        (Equiv.Set.sumCompl (Set.range P₀.map)))
  let e : Fin (n + (d + k)) ≃ Fin n ⊕ ι :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) e₀)
  let f : Fin (n + d) ≃ Fin n ⊕ σ :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) es)
  have hc : n + d ≤ n + (d + k) := by omega
  refine ⟨d + k, n + d, hc, P.reindex e f, by omega, ?_, ?_⟩
  · change e.symm ∘ P.map ∘ f = Fin.castLE hc
    apply funext
    intro j
    apply e.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective j
    cases i with
    | inl i =>
      simp only [f, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.refl_apply,
        Sum.map_inl, finSumFinEquiv_apply_left, finSumFinEquiv_symm_apply_castAdd]
      change Sum.inl i = e (Fin.castLE hc (Fin.castAdd d i))
      have hcast : Fin.castLE hc (Fin.castAdd d i) = Fin.castAdd (d + k) i := rfl
      simp [hcast, e]
    | inr i =>
      simp only [f, Equiv.trans_apply, Equiv.sumCongr_apply,
        Sum.map_inr, finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_natAdd]
      change Sum.inr (P₀.map (es i)) = e (Fin.castLE hc (Fin.natAdd n i))
      have hcast : Fin.castLE hc (Fin.natAdd n i) =
          Fin.natAdd n (Fin.castAdd k i) := rfl
      simp only [hcast, e, e₀, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
        Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_symm_apply_castAdd,
        Sum.map_inl, Equiv.ofInjective_apply]
      rfl
  · intro i
    change P.val (e (Fin.castAdd (d + k) i)) = a i
    simp [e, P, SubmersivePresentation.comp, PreSubmersivePresentation.comp,
      Presentation.comp, Generators.comp, Q, Q₁]

end Algebra
