/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.FreeComplexBaseLift
import WeilConjectures.AlgebraicGeometry.FreeComplexExtendFamily

/-! # A complex of free modules maps to a resolution

## References

* Stacks Project, Tag 00LS.
-/

@[expose] public section

universe u v w

open CategoryTheory

/-- A complex of free modules over `M` maps to an exact resolution of `N`.
(Stacks, Tag 00LS) -/
theorem free_complex_maps_to_resolution
    (R : Type u) [CommRing R]
    (M N : ModuleCat R) (φ : M ⟶ N)
    (N' : ℕ → ModuleCat R)
    (d : ∀ i : ℕ, N' (i + 1) ⟶ N' i)
    (η : N' 0 ⟶ N)
    (hd0 : d 0 ≫ η = 0)
    (hd : ∀ i : ℕ, d (i + 1) ≫ d i = 0)
    (hη : Function.Surjective η)
    (hex0 : (ShortComplex.mk (d 0) η hd0).Exact)
    (hex : ∀ i : ℕ, (ShortComplex.mk (d (i + 1)) (d i) (hd i)).Exact)
    (F : ℕ → ModuleCat R)
    (δ : ∀ i : ℕ, F (i + 1) ⟶ F i)
    (π : F 0 ⟶ M)
    (hδ0 : (δ 0) ≫ π = 0)
    (hδ : ∀ i : ℕ, (δ (i + 1)) ≫ (δ i) = 0)
    (hfree : ∀ i : ℕ, Module.Free R (F i)) :
    ∃ α : ∀ i : ℕ, F i ⟶ N' i,
      α 0 ≫ η = π ≫ φ ∧
        (∀ i : ℕ, (α (i + 1)) ≫ d i = (δ i) ≫ α i) := by
  obtain ⟨a₀, ha₀⟩ := free_complex_base_lift R M N φ N' η F π hη (hfree 0)
  have hstart : δ 0 ≫ a₀ ≫ η = 0 := by
    rw [ha₀, ← Category.assoc, hδ0, Limits.zero_comp]
  obtain ⟨α, hα₀, hα⟩ :=
    free_complex_extend_family R N N' d η hd0 hd hex0 hex F δ hδ hfree a₀ hstart
  refine ⟨α, ?_, hα⟩
  rw [hα₀, ha₀]
