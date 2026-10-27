/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
import Sheaf.TraceFormula.RationalConeDualFinite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Integral dual forms for pointed rational cones

Source: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, Remark 3.1.29, printed p. 103; the integral lattice formulation is
expanded from the rational polyhedral cone description (Kato 1994, *Toric singularities*).
(blueprint: lem-trf-rational-cone-dual-integral-forms)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-- Clear denominators on a finite integral basis, then extend the resulting values linearly. -/
private theorem integral_multiple
    (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (f : L →ₗ[ℤ] ℚ) :
    ∃ (d : ℤ), 0 < d ∧ ∃ φ : L →+ ℤ, ∀ x, (d : ℚ) * f x = (φ x : ℚ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.pos ℤ) (fun j ↦ f (b j))
  choose a ha using hd
  let p : L →ₗ[ℤ] ℤ := b.constr ℤ a
  have hp : (Int.castAddHom ℚ).toIntLinearMap.comp p = (d : ℤ) • f := by
    apply b.ext
    intro j
    simpa [p] using ha j
  refine ⟨d, d.property, p.toAddMonoidHom, fun x ↦ ?_⟩
  simpa [zsmul_eq_mul] using (LinearMap.congr_fun hp x).symm

/--
(blueprint: lem-trf-rational-cone-dual-integral-forms)
Source: `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
Expose VIII, Remark 3.1.29, printed p. 103 (Kato 1994, *Toric singularities*, WANTED).

Let `L` be a finite free abelian group, `V = ℚ ⊗[ℤ] L` (canonically `L ⊗[ℤ] ℚ`), and
let `C ⊆ V` be the cone of nonnegative rational combinations of `v₁, …, vₘ ∈ L`
(`m = 0` allowed).  If `C` is pointed and every vector of `V` is a difference of two
elements of `C`, then there are `r ≥ 0` and homomorphisms `φᵢ : L → ℤ` whose rational
extensions `Φᵢ` span `Hom_ℚ(V, ℚ)` and cut out `C` by `Φᵢ ≥ 0`.  When `V = 0` the family
is empty; when `V ≠ 0` every such family has `r ≥ 1`.

Proof (from the DAG node).
1. By `lem-trf-rational-cone-dual-finite`, applied to `V` and the `vⱼ`, there are finitely
   many rational forms `λᵢ : V → ℚ` with `C = {x | λᵢ x ≥ 0 for all i}`.  If `V = 0`, take
   the empty family; assume `V ≠ 0`.
2. Write each `λᵢ` in the dual of a `ℤ`-basis of `L` and multiply it by a positive integer
   `dᵢ` clearing denominators; `φᵢ = dᵢ λᵢ` maps `L` into `ℤ`, and the nonnegative locus
   and the `ℚ`-span are unchanged.
3. If `x` is killed by every `φᵢ`, then `x` and `-x` lie in `C`, so `x = 0` by pointedness;
   a family with zero common kernel spans the dual in finite dimension.  As `V ≠ 0`, its
   dual is nonzero, so a spanning family is nonempty: `r ≥ 1`.
-/
theorem rationalConeDualIntegralForms
    (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (m : ℕ) (v : Fin m → L) :
    let V := ℚ ⊗[ℤ] L
    let C : Set V := {x | ∃ q : Fin m → ℚ≥0,
      x = ∑ j, (q j : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) (v j)}
    (C ∩ (-C) = ({0} : Set V)) →
      (∀ x : V, ∃ c₁ ∈ C, ∃ c₂ ∈ C, x = c₁ - c₂) →
      (∃ (r : ℕ) (φ : Fin r → L →+ ℤ) (Φ : Fin r → V →ₗ[ℚ] ℚ),
        (∀ (i : Fin r) (ℓ : L),
          Φ i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ i ℓ : ℚ)) ∧
        Submodule.span ℚ (Set.range Φ) = ⊤ ∧
        C = {x | ∀ i, 0 ≤ Φ i x} ∧
        ((∀ x : V, x = 0) → r = 0)) ∧
      ((∃ x : V, x ≠ 0) →
        ∀ (r : ℕ) (φ : Fin r → L →+ ℤ) (Φ : Fin r → V →ₗ[ℚ] ℚ),
          (∀ (i : Fin r) (ℓ : L),
            Φ i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ i ℓ : ℚ)) →
          Submodule.span ℚ (Set.range Φ) = ⊤ →
          C = {x | ∀ i, 0 ≤ Φ i x} → 0 < r) := by
  classical
  dsimp only
  let V := ℚ ⊗[ℤ] L
  let C : Set V := {x | ∃ q : Fin m → ℚ≥0,
    x = ∑ j, (q j : ℚ) • TensorProduct.tmul ℤ (1 : ℚ) (v j)}
  intro hpoint _hgen
  have hC0 : (0 : V) ∈ C := by
    exact ⟨fun _ ↦ 0, by simp⟩
  have hnonempty : (∃ x : V, x ≠ 0) →
      ∀ (r : ℕ) (φ : Fin r → L →+ ℤ) (Φ : Fin r → V →ₗ[ℚ] ℚ),
        (∀ (i : Fin r) (ℓ : L),
          Φ i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ i ℓ : ℚ)) →
        Submodule.span ℚ (Set.range Φ) = ⊤ →
        C = {x | ∀ i, 0 ≤ Φ i x} → 0 < r := by
    rintro ⟨x, hx⟩ r φ Φ _ _ hC
    by_contra hr
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst r
    have hmem (y : V) : y ∈ C := by
      rw [hC]
      exact fun i ↦ Fin.elim0 i
    have : x ∈ C ∩ (-C) := ⟨hmem x, by simpa using hmem (-x)⟩
    rw [hpoint] at this
    exact hx (Set.mem_singleton_iff.mp this)
  refine ⟨?_, hnonempty⟩
  by_cases hzero : ∀ x : V, x = 0
  · have : Subsingleton V := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
    refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, fun _ ↦ rfl⟩
    · exact fun i ↦ Fin.elim0 i
    · exact Subsingleton.elim _ _
    · ext x
      simp only [Set.mem_ofPred_eq, Fin.forall_fin_zero, iff_true]
      change x ∈ C
      rw [hzero x]
      exact hC0
  · obtain ⟨r, forms, hforms⟩ := Weil.rationalConeDualFinite m
      (fun j ↦ TensorProduct.tmul ℤ (1 : ℚ) (v j))
    have hdesc : ∀ x : V, x ∈ C ↔ ∀ i, 0 ≤ forms i x := by
      intro x
      rw [← hforms x]
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨fun j ↦ (q j : ℚ), fun j ↦ (q j).property, hq.symm⟩
      · rintro ⟨q, hq, hx⟩
        exact ⟨fun j ↦ ⟨q j, hq j⟩, hx.symm⟩
    have hclear (i : Fin r) : ∃ (d : ℤ), 0 < d ∧ ∃ φ : L →+ ℤ,
        ∀ ℓ, (d : ℚ) * forms i (TensorProduct.tmul ℤ (1 : ℚ) ℓ) = (φ ℓ : ℚ) := by
      exact integral_multiple L
        (((forms i).restrictScalars ℤ).comp (TensorProduct.mk ℤ ℚ L (1 : ℚ)))
    choose d hd φ hφ using hclear
    let Φ : Fin r → V →ₗ[ℚ] ℚ := fun i ↦ (d i : ℚ) • forms i
    have hΦ : C = {x | ∀ i, 0 ≤ Φ i x} := by
      ext x
      rw [hdesc]
      simp only [Set.mem_ofPred_eq, Φ, LinearMap.smul_apply, smul_eq_mul]
      exact forall_congr' fun i ↦ (mul_nonneg_iff_of_pos_left (by exact_mod_cast hd i)).symm
    have hker : (Submodule.span ℚ (Set.range Φ)).dualCoannihilator = ⊥ := by
      apply bot_unique
      intro x hx
      rw [Submodule.mem_bot]
      have hx0 (i : Fin r) : Φ i x = 0 :=
        (Submodule.mem_dualCoannihilator x).mp hx _ (Submodule.subset_span ⟨i, rfl⟩)
      have hmem : x ∈ C ∩ (-C) := by
        constructor
        · rw [hΦ]
          exact fun i ↦ (hx0 i).ge
        · have hn : -x ∈ C := by
            rw [hΦ]
            intro i
            simp [hx0 i]
          simpa using hn
      rw [hpoint] at hmem
      exact Set.mem_singleton_iff.mp hmem
    refine ⟨r, φ, Φ, fun i ℓ ↦ hφ i ℓ, ?_, hΦ, fun hz ↦ (hzero hz).elim⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := Submodule.span ℚ (Set.range Φ)), hker, Submodule.dualAnnihilator_bot]

end
