/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.BrauerScalarDefect
import WeilConjectures.FieldTheory.CocycleMonomialCoefficients
import WeilConjectures.FieldTheory.ProjectiveMatrixDescent

/-!
# Crossed-product data for a continuous Galois cocycle

## Main results

- `Field.exists_crossedProduct_data_for_cocycle`: a continuous two-cocycle with values in the
  units of the separable closure gives a central simple algebra together with splitting and
  scalar-defect data for it.

## Implementation details

The cocycle is inflated from a cocycle `c` on `Γ = Gal(L/K)` for a finite Galois extension `L`.
On `L^Γ` the monomial matrices `B(g) e_j = c(g, j) e_(gj)` satisfy
`B(g) g(B(h)) = c(g, h) B(gh)`, and `B(1)` is scalar, so `M ↦ B(g) g(M) B(g)⁻¹` is a semilinear
action on the matrix algebra; its invariants form the central simple algebra, by Galois descent.

## References

* Stacks Project, Theorem 03R7 (surjectivity) and Section 0DVG.
-/

@[expose] public section

universe u

namespace Field

open scoped TensorProduct

private def monomialLift {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p : Equiv.Perm ι) (w : ι → Rˣ) :
    Matrix.GeneralLinearGroup ι R where
  val i j := if i = p j then (w j).val else 0
  inv i j := if p i = j then (w i).inv else 0
  val_inv := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (p.symm i)]
    · simp
    · intro k _ hk
      have hi : i ≠ p k := by
        intro h
        apply hk
        exact (p.symm_apply_apply k).symm.trans (congrArg p.symm h.symm)
      simp [hi]
    · simp
  inv_val := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (p i)]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [p.injective.eq_iff, hij]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp

private theorem monomialLift_mul_map {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p r : Equiv.Perm ι) (w v : ι → Rˣ) (f : R →+* R) :
    monomialLift p w * Matrix.GeneralLinearGroup.map f (monomialLift r v) =
      monomialLift (p * r) (fun j ↦ w (r j) * Units.map f (v j)) := by
  apply Units.ext
  ext i j
  change (∑ k, (if i = p k then (w k).val else 0) *
    f (if k = r j then (v j).val else 0)) =
      if i = (p * r) j then (w (r j) * Units.map f (v j)).val else 0
  rw [Finset.sum_eq_single (r j)]
  · simp [Equiv.Perm.mul_apply, ite_mul]
  · intro k _ hk
    simp [hk]
  · simp

private theorem monomialLift_scalar_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (p : Equiv.Perm ι) (w : ι → Rˣ) (t : Rˣ) :
    monomialLift p (fun j ↦ t * w j) =
      Matrix.GeneralLinearGroup.scalar ι t * monomialLift p w := by
  apply Units.ext
  ext i j
  simp [monomialLift, Matrix.scalar, Matrix.diagonal_mul, mul_ite]

private theorem scalar_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (t : Rˣ) (M : Matrix ι ι R) :
    (Matrix.GeneralLinearGroup.scalar ι t).val * M *
      ((Matrix.GeneralLinearGroup.scalar ι t)⁻¹).val = M := by
  rw [show (Matrix.GeneralLinearGroup.scalar ι t).val * M =
    M * (Matrix.GeneralLinearGroup.scalar ι t).val from
      Matrix.scalar_comm _ (Commute.all _) M]
  rw [mul_assoc, (Matrix.GeneralLinearGroup.scalar ι t).mul_inv, mul_one]

private theorem scalar_mul_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (t : Rˣ) (B : Matrix.GeneralLinearGroup ι R)
    (M : Matrix ι ι R) :
    (Matrix.GeneralLinearGroup.scalar ι t * B).val * M *
      ((Matrix.GeneralLinearGroup.scalar ι t * B)⁻¹).val =
        B.val * M * (B⁻¹).val := by
  simpa only [Units.val_mul, mul_inv_rev, mul_assoc] using
    scalar_conjugation t (B.val * M * (B⁻¹).val)

set_option linter.unusedVariables false in
/-- For a continuous homogeneous two-cocycle `z` of the absolute Galois group with values in the
units of the separable closure `Kˢ`, there are a central simple algebra `A`, a splitting
`e : Kˢ ⊗[K] A ≃ Mat_n(Kˢ)` with `n ≠ 0` and a locally constant `b : Gal(Kˢ/K) → GLₙ(Kˢ)` such
that `g(e(1 ⊗ a)) = b(g)⁻¹ e(1 ⊗ a) b(g)` and `b(g) g(b(h)) = c(g, h) b(gh)`, where `c` is the
cocycle value of `z`. -/
theorem exists_crossedProduct_data_for_cocycle (K : Type u) [Field K]
    (z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2) :
    ∃ (A : CSA.{u, u} K) (n : ℕ) (hn : n ≠ 0)
      (e : (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin n) (Fin n) (SeparableClosure K))
      (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
        Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K)),
      IsLocallyConstant b ∧
      (∀ (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : A),
        (e (1 ⊗ₜ[K] a)).map g =
          ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val) ∧
      (∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
          b (g * h)) := by
  obtain ⟨n, hn, p, w, hw, hdef⟩ := exists_cocycle_monomial_coefficients K z
  let b := fun g ↦ monomialLift (p g) (w g)
  have hb : IsLocallyConstant b := hw.comp (fun t ↦ monomialLift t.1 t.2)
  have hd : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) =
      Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z g h) *
        b (g * h) := by
    intro g h
    change monomialLift (p g) (w g) *
      Matrix.GeneralLinearGroup.map g.toRingHom (monomialLift (p h) (w h)) = _
    rw [monomialLift_mul_map, ← p.map_mul]
    have hc : (fun j ↦ w g (p h j) * Units.map g.toRingHom (w h j)) =
        (fun j ↦ galoisUnitsCocycleValue K z g h * w (g * h) j) := by
      funext j
      exact hdef g h j
    rw [hc, monomialLift_scalar_mul]
  have h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M := by
    have hh := hd 1 1
    change b 1 * b 1 =
      Matrix.GeneralLinearGroup.scalar (Fin n) (galoisUnitsCocycleValue K z 1 1) * b 1 at hh
    have hb1 := mul_right_cancel hh
    intro M
    rw [hb1]
    exact scalar_conjugation _ M
  have hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val := by
    intro g h M
    calc
      _ = (b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h)).val *
          M.map (g * h) *
          ((b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h))⁻¹).val := by
        change (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g *
          ((b g)⁻¹).val = ((b g).val * (b h).val.map g) * M.map (g * h) *
            (((b h)⁻¹).val.map g * ((b g)⁻¹).val)
        simp only [Matrix.map_mul, Matrix.map_map, mul_assoc]
        rfl
      _ = _ := by
        rw [hd g h]
        exact scalar_mul_conjugation _ _ _
  obtain ⟨A, e, he⟩ := exists_CSA_of_matrix_descent_action K n hn b hb h1 hm
  exact ⟨A, n, hn, e, b, hb, he, hd⟩

end Field
