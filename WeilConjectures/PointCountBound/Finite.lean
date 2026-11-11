/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCountBound
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Bounded point counts of finite schemes

A finite scheme `X` over a finite field `k` has a bounded number of points over the finite
extensions of `k`: a `k_n`-point is a `k`-algebra map `Γ(X, ⊤) → k_n`, and there are at most
`dim_k Γ(X, ⊤)` of these by the linear independence of characters. Together with the linear
growth of the point count of an affine curve
(`AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_mul_pow`), this is blueprint
`lemma-point-count-bound`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_of_isFinite`: the bound for a finite
  scheme.
- `AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_mul_pow_and_exists_pointCount_le`: both
  bounds together.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [Finite k]

/-- Blueprint `lemma-point-count-bound--2`: for a finite scheme `X` over a finite field `k`, the
number of points of `X` rational over the degree `n` extension `k_n` of `k` is bounded
independently of `n`.

If `Γ(X, ⊤)` is spanned by `d` elements over `k`, then a `k_n`-point of `X` is a `k`-algebra map
`Γ(X, ⊤) → k_n`, determined by its values on the `d` generators, and these maps are linearly
independent characters, so there are at most `d` of them. -/
theorem Hom.exists_pointCount_le_of_isFinite {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsFinite f] : ∃ d : ℕ, ∀ n : ℕ, f.pointCount n ≤ d := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) :=
    (f.finite_appTop).comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  obtain ⟨d, r, hr⟩ := Module.Finite.exists_fin (R := k) (M := Γ(X, ⊤))
  refine ⟨d, fun n ↦ ?_⟩
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  obtain ⟨hR, hRcard⟩ := natCard_algHom_le_mul_natCard_algHom
    (L := FiniteField.galoisExtension k n) (k := k) (A := k) r hr
  obtain ⟨j, hj⟩ := f.exists_injective_fieldPoints_algHom (FiniteField.galoisExtension k n)
  calc f.pointCount n ≤ Nat.card (Γ(X, ⊤) →ₐ[k] FiniteField.galoisExtension k n) :=
        Nat.card_le_card_of_injective j hj
    _ ≤ d := by simpa using hRcard

/-- Blueprint `lemma-point-count-bound`: a point-count bound.

For a smooth affine curve `U₀` over a finite field `k` with `q` elements there is a constant `D`
with `#U₀(k_n) ≤ D q ^ n` for all `n ≥ 1`
(`AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_mul_pow`, blueprint
`lemma-point-count-bound--1`); for a finite `k`-scheme `Z`, the number of `k_n`-points is
bounded independently of `n` (`AlgebraicGeometry.Scheme.Hom.exists_pointCount_le_of_isFinite`,
blueprint `lemma-point-count-bound--2`). -/
theorem Hom.exists_pointCount_le_mul_pow_and_exists_pointCount_le {U Z : Scheme.{u}}
    (f : U ⟶ Spec (.of k)) [IsAffine U] [SmoothOfRelativeDimension 1 f]
    (g : Z ⟶ Spec (.of k)) [IsFinite g] :
    (∃ d : ℕ, ∀ n : ℕ, n ≠ 0 → f.pointCount n ≤ d * Nat.card k ^ n) ∧
      ∃ d : ℕ, ∀ n : ℕ, g.pointCount n ≤ d := by
  have := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨f.exists_pointCount_le_mul_pow (by
      exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension f 1),
    g.exists_pointCount_le_of_isFinite⟩

end AlgebraicGeometry.Scheme
