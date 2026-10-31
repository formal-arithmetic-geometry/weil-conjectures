/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.CompositionSeries
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Filtrations and spectra

Source: the latest Weil conjectures blueprint, `sec-purity-real-sheaves`,
`sk-p-linear-filtration`, including its complement (blueprint: sk-p-linear-filtration).

The explicit filtration factorization and its multiplicity statement are stated here.
The finite-free ring complement, scalar-subquotient assertion, tensor/exterior/contragredient
root formulas, and diagonal exterior-basis formula use the existing declarations listed in
the node's `lean.declarations`, rather than duplicate statements.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LinearMap

/-- An automorphism preserving a finite filtration has reverse characteristic polynomial equal
to the product over its successive quotients, and its eigenvalue multiset is the sum of the
multisets on those quotients.

Source: latest blueprint, `sec-purity-real-sheaves/sk-p-linear-filtration/_section.md`
(blueprint: sk-p-linear-filtration).

Proof plan: use the coefficient conventions of `det-d-linear`. Extend the filtration constantly
after `n` by `G j = F (min j n)` and apply the iterated invariant-subspace factorization
`LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le` (`p-linear-filtration`); reindex the range
product over `Fin n`. Reversal commutes with finite products over a field
(`def-weil-reverse-characteristic-polynomial`), giving the reverse characteristic polynomial
identity. All factors are monic (`lem-weil-pbc-charpoly-free-module-properties`), so the product
is nonzero and its root multiset is the sum of the root multisets, including multiplicities.
The zero filtration and zero graded pieces contribute the empty root multiset. -/
theorem filtration_charpolyRev_and_roots
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (u : V ≃ₗ[K] V) (n : ℕ) (F : Fin (n + 1) → Submodule K V)
    (h0 : F 0 = ⊥) (hn : F (Fin.last n) = ⊤)
    (hle : ∀ i : Fin n, F i.castSucc ≤ F i.succ)
    (hF : ∀ i, F i ≤ (F i).comap (u : V →ₗ[K] V)) :
    (u : V →ₗ[K] V).charpolyRev = ∏ i : Fin n,
      (((F i.castSucc).comap (F i.succ).subtype).mapQ
        ((F i.castSucc).comap (F i.succ).subtype)
        ((u : V →ₗ[K] V).restrict (hF i.succ))
        (fun _ hx ↦ hF i.castSucc hx)).charpolyRev ∧
    (u : V →ₗ[K] V).charpoly.roots = ∑ i : Fin n,
      (((F i.castSucc).comap (F i.succ).subtype).mapQ
        ((F i.castSucc).comap (F i.succ).subtype)
        ((u : V →ₗ[K] V).restrict (hF i.succ))
        (fun _ hx ↦ hF i.castSucc hx)).charpoly.roots := by
  classical
  let G : ℕ → Submodule K V := fun j ↦
    F ⟨min j n, Nat.lt_succ_of_le (Nat.min_le_right j n)⟩
  have hG0 : G 0 = ⊥ := by simpa [G] using h0
  have hGn : G n = ⊤ := by
    calc
      G n = F (Fin.last n) := congrArg F (Fin.ext (by simp))
      _ = ⊤ := hn
  have hGle : ∀ i < n, G i ≤ G (i + 1) := by
    intro i hi
    simpa [G, Nat.min_eq_left (Nat.le_of_lt hi),
      Nat.min_eq_left (Nat.succ_le_of_lt hi)] using hle ⟨i, hi⟩
  have hGu : ∀ i, G i ≤ (G i).comap (u : V →ₗ[K] V) := fun i ↦ hF _
  have hchar := LinearMap.charpoly_eq_prod_charpoly_mapQ_of_le
    (u : V →ₗ[K] V) G n hG0 hGn hGle hGu
  let q (i : Fin n) :=
    (((F i.castSucc).comap (F i.succ).subtype).mapQ
      ((F i.castSucc).comap (F i.succ).subtype)
      ((u : V →ₗ[K] V).restrict (hF i.succ)) (fun _ hx ↦ hF i.castSucc hx))
  have hchar' : (u : V →ₗ[K] V).charpoly = ∏ i : Fin n, (q i).charpoly := by
    rw [← Fin.prod_univ_eq_prod_range] at hchar
    refine hchar.trans (Finset.prod_congr rfl fun i _ ↦ ?_)
    have hi0 : (⟨min (i : ℕ) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
        Fin (n + 1)) = i.castSucc := Fin.ext (Nat.min_eq_left (Nat.le_of_lt i.isLt))
    have hi1 : (⟨min ((i : ℕ) + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ :
        Fin (n + 1)) = i.succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.isLt))
    exact congrArg₂ (fun a b : Fin (n + 1) ↦
      (((F a).comap (F b).subtype).mapQ ((F a).comap (F b).subtype)
        ((u : V →ₗ[K] V).restrict (hF b)) (fun _ hx ↦ hF a hx)).charpoly) hi0 hi1
  change (u : V →ₗ[K] V).charpolyRev = ∏ i : Fin n, (q i).charpolyRev ∧
    (u : V →ₗ[K] V).charpoly.roots = ∑ i : Fin n, (q i).charpoly.roots
  constructor
  · simp only [LinearMap.charpolyRev_def]
    rw [hchar', Polynomial.reverse_prod_of_domain]
  · rw [hchar', Polynomial.roots_prod]
    · rfl
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (q i).charpoly_monic.ne_zero

/-- If `α` is an eigenvalue of `u`, its `n`-th power is an eigenvalue on the `n`-fold tensor
power, including the zeroth tensor power over the coefficient field.

Source: latest blueprint, `sec-purity-real-sheaves/sk-p-linear-filtration/_section.md`,
complement (blueprint: sk-p-linear-filtration).

Proof plan (`p-linear-spectra`): choose a nonzero `α`-eigenvector `x` and take the pure tensor
with every entry `x`. A linear functional taking `x` to 1, tensorized in every factor, shows
that this tensor is nonzero. `PiTensorProduct.map_tprod` and multilinearity give eigenvalue
`α ^ n`. For `n = 0`, the empty tensor is 1 in the coefficient field and the map is the
identity; the same functional argument applies. Equivalently iterate the tensor-product
spectrum formula of `p-linear-spectra`. -/
theorem hasEigenvalue_tensorPower_of_hasEigenvalue
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (u : V ≃ₗ[K] V) {α : K} (hα : Module.End.HasEigenvalue (u : V →ₗ[K] V) α) (n : ℕ) :
    Module.End.HasEigenvalue
      (PiTensorProduct.map (fun _ : Fin n ↦ (u : V →ₗ[K] V))) (α ^ n) := by
  classical
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hx.2
  let t := PiTensorProduct.tprod K (fun _ : Fin n ↦ x)
  have ht : t ≠ 0 := by
    let ψ := PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap fun _ ↦ φ)
    have heval : ψ t = 1 := by
      simp [ψ, t, hφ]
    intro hz
    simp [hz] at heval
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := t)
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ht⟩
  simp only [t, PiTensorProduct.map_tprod, hx.apply_eq_smul]
  simpa using (PiTensorProduct.tprod K).map_smul_univ
    (fun _ : Fin n ↦ α) (fun _ : Fin n ↦ x)

end LinearMap
