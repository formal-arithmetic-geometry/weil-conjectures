/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Inductions

/-!

# Hensel's and Newton's lemmas over henselian local rings without monicity

Mathlib's `HenselianLocalRing` asks for roots of monic polynomials only. We prove:

* **Hensel's lemma** (`HenselianLocalRing.exists_isRoot_sub_mem`): over a henselian local ring
  `R`, a polynomial `f`, monic or not, with `f(a₀) ∈ 𝔪` and `f'(a₀)` a unit has a root
  `a ≡ a₀ (mod 𝔪)`. After a translation and the rescaling `X ↦ f(a₀) X`, the polynomial is
  `1 + c₁ X + (terms in 𝔪)`, whose reflection is monic with the simple residual root `-c̄₁`.
* **Newton's lemma** (`HenselianLocalRing.exists_isRoot_of_eval_eq_sq_mul`): if
  `f(a) = f'(a)² c` with `c ∈ 𝔪`, then `f` has a root `b` with `b - a ∈ f'(a) 𝔪`. This is the form
  of Hensel's lemma for roots that are not simple modulo `𝔪`, used to compare separable
  extensions of a henselian discretely valued field with those of its completion (SGA 4½,
  [Th. finitude], Lemme 3.3).

-/

@[expose] public section

universe u

open Polynomial IsLocalRing

namespace HenselianLocalRing

variable {R : Type u} [CommRing R] [HenselianLocalRing R]

/-- A polynomial `1 + c₁ X + (terms of degree ≥ 2 in 𝔪)` with `c₁` a unit over a henselian local
ring has a root which is a unit. -/
theorem exists_isUnit_isRoot_of_coeff (k : R[X]) (h₀ : k.coeff 0 = 1) (h₁ : IsUnit (k.coeff 1))
    (h₂ : ∀ i, 2 ≤ i → k.coeff i ∈ maximalIdeal R) : ∃ w, IsUnit w ∧ k.IsRoot w := by
  set c := k.coeff 1
  have hdeg : 1 ≤ k.natDegree := le_natDegree_of_ne_zero h₁.ne_zero
  set n := k.natDegree
  let M := reflect (n + 1) k
  have hM : M.Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one (n + 1) ?_ ?_
    · exact natDegree_reflect_le.trans (by omega)
    · rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, h₀]
  have hk : k.map (residue R) = C 1 + C (residue R c) * X := by
    ext i
    rw [coeff_map]
    rcases i with _ | _ | i
    · simp [h₀]
    · simp [c, coeff_one]
    · rw [(residue_eq_zero_iff _).2 (h₂ _ (by omega))]
      simp [coeff_one]
  have hMmap : M.map (residue R) = X ^ n * (X + C (residue R c)) := by
    rw [← reflect_map, hk, reflect_add, reflect_C, ← pow_one (X : (ResidueField R)[X]),
      reflect_C_mul_X_pow, revAt_le (by omega)]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, show m + 1 + 1 - 1 = m + 1 by omega]
    simp only [map_one, one_mul]
    ring
  have hc : residue R c ≠ 0 := (residue_ne_zero_iff_isUnit _).2 h₁
  have H := ((HenselianLocalRing.TFAE R).out 0 1).mp (by infer_instance)
  obtain ⟨v, hv, hvres⟩ := H M hM (-residue R c) (by
      rw [aeval_def, eval₂_eq_eval_map, ResidueField.algebraMap_eq, hMmap]
      simp) (by
      rw [aeval_def, eval₂_eq_eval_map, ResidueField.algebraMap_eq, ← derivative_map, hMmap,
        derivative_mul]
      simp [hc])
  have hvu : IsUnit v := (residue_ne_zero_iff_isUnit _).1 (by rw [hvres]; exact neg_ne_zero.2 hc)
  let w := hvu.unit⁻¹
  have : Invertible (w : R) := w.invertible
  have h := (eval₂_reflect_eq_zero_iff (RingHom.id R) (w : R) (n + 1) k (by omega)).1
  have hw : ⅟(w : R) = v := by simp [w]
  refine ⟨w, w.isUnit, h ?_⟩
  rw [hw]
  exact hv

omit [HenselianLocalRing R] in
/-- The decomposition `g = g(0) + X (g'(0) + X G)` of a polynomial. -/
lemma _root_.Polynomial.eq_C_add_X_mul_C_add_X_mul (g : R[X]) :
    g = C (g.coeff 0) + X * (C (g.coeff 1) + X * g.divX.divX) := by
  conv_lhs => rw [← X_mul_divX_add g, ← X_mul_divX_add g.divX]
  rw [coeff_divX]
  ring

/-- **Hensel's lemma without monicity**: over a henselian local ring, a polynomial `f` with
`f(a₀) ∈ 𝔪` and `f'(a₀)` a unit has a root `a ≡ a₀ (mod 𝔪)`. -/
theorem exists_isRoot_sub_mem (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ maximalIdeal R)
    (h₂ : IsUnit (f.derivative.eval a₀)) : ∃ a, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  set g := taylor a₀ f
  set c₀ := g.coeff 0
  set c₁ := g.coeff 1
  have hc₀ : c₀ = f.eval a₀ := taylor_coeff_zero a₀ f
  have hc₁ : c₁ = f.derivative.eval a₀ := taylor_coeff_one a₀ f
  set G := g.divX.divX
  let k : R[X] := 1 + C c₁ * X + C c₀ * (X ^ 2 * G.comp (C c₀ * X))
  have hgk : g.comp (C c₀ * X) = C c₀ * k := by
    conv_lhs => rw [g.eq_C_add_X_mul_C_add_X_mul]
    simp only [add_comp, mul_comp, C_comp, X_comp, k]
    ring
  have hk₀ : k.coeff 0 = 1 := by simp [k, coeff_one]
  have hk₁ : k.coeff 1 = c₁ := by simp [k, coeff_one, coeff_C_mul, coeff_X_pow_mul']
  have hk₂ : ∀ i, 2 ≤ i → k.coeff i ∈ maximalIdeal R := by
    intro i hi
    have : k.coeff i = c₀ * (X ^ 2 * G.comp (C c₀ * X)).coeff i := by
      simp [k, coeff_one, coeff_C_mul, coeff_X, show i ≠ 0 by omega, show 1 ≠ i by omega]
    rw [this]
    exact Ideal.mul_mem_right _ _ (hc₀ ▸ h₁)
  obtain ⟨w, -, hw⟩ := exists_isUnit_isRoot_of_coeff k hk₀ (hk₁ ▸ hc₁ ▸ h₂) hk₂
  refine ⟨c₀ * w + a₀, ?_, by rw [add_sub_cancel_right]; exact Ideal.mul_mem_right _ _ (hc₀ ▸ h₁)⟩
  have := congrArg (eval w) hgk
  rw [eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_C, hw.eq_zero, mul_zero, taylor_eval]
    at this
  exact this

/-- **Newton's lemma over a henselian local ring**: if `f(a) = f'(a)² c` with `c ∈ 𝔪`, then `f`
has a root `b` with `b - a = f'(a) y` for some `y ∈ 𝔪`. -/
theorem exists_isRoot_of_eval_eq_sq_mul (f : R[X]) (a c : R) (hc : c ∈ maximalIdeal R)
    (h : f.eval a = f.derivative.eval a ^ 2 * c) :
    ∃ b, f.IsRoot b ∧ ∃ y ∈ maximalIdeal R, b - a = f.derivative.eval a * y := by
  set d := f.derivative.eval a
  set g := taylor a f
  have hg₀ : g.coeff 0 = d ^ 2 * c := by rw [taylor_coeff_zero, h]
  have hg₁ : g.coeff 1 = d := taylor_coeff_one a f
  set G := g.divX.divX
  let k : R[X] := C c + X + X ^ 2 * G.comp (C d * X)
  have hgk : g.comp (C d * X) = C (d ^ 2) * k := by
    conv_lhs => rw [g.eq_C_add_X_mul_C_add_X_mul, hg₀, hg₁]
    simp only [add_comp, mul_comp, C_comp, X_comp, k, C_mul, C_pow, pow_comp]
    ring
  obtain ⟨y, hy, hy₀⟩ := exists_isRoot_sub_mem k 0 (by simpa [k] using hc) (by simp [k])
  rw [sub_zero] at hy₀
  refine ⟨d * y + a, ?_, y, hy₀, by rw [add_sub_cancel_right]⟩
  have := congrArg (eval y) hgk
  rw [eval_comp, eval_mul, eval_C, eval_X, eval_mul, eval_C, hy.eq_zero, mul_zero, taylor_eval]
    at this
  exact this

end HenselianLocalRing
