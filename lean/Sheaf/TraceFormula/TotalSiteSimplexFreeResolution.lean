/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Exact augmented free simplex module complex

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C, with the component
formula from Tag 0D72 (blueprint: lem-trf-total-site-simplex-free-resolution).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The direct sum of copies of `M` indexed by monotone maps `[p] → [m]`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
abbrev simplexModule (Λ : Type u) [CommRing Λ] (m p : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :=
  DirectSum (SimplexCategory.mk p ⟶ SimplexCategory.mk m) (fun _ ↦ M)

/-- The map on direct sums induced by the `i`-th face.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
noncomputable def simplexFaceLinear (Λ : Type u) [CommRing Λ] (m p : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] (i : Fin (p + 2)) :
    simplexModule Λ m (p + 1) M →ₗ[Λ] simplexModule Λ m p M :=
  DirectSum.toModule Λ _ _ (fun α ↦
    DirectSum.lof Λ _ (fun _ ↦ M) (SimplexCategory.δ i ≫ α))

/-- The alternating face differential in degree `p`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
noncomputable def simplexDifferential (Λ : Type u) [CommRing Λ] (m p : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    simplexModule Λ m (p + 1) M →ₗ[Λ] simplexModule Λ m p M :=
  ∑ i : Fin (p + 2), ((-1 : Λ) ^ (i : ℕ)) • simplexFaceLinear Λ m p M i

/-- The face differential squares to zero.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
 theorem simplexDifferential_squared (Λ : Type u) [CommRing Λ] (m p : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    simplexDifferential Λ m p M ∘ₗ simplexDifferential Λ m (p + 1) M = 0 := by
  sorry

/-- The fold augmentation from degree zero to `M`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
noncomputable def simplexAugmentation (Λ : Type u) [CommRing Λ] (m : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    simplexModule Λ m 0 M →ₗ[Λ] M :=
  DirectSum.toModule Λ _ M (fun _ ↦ LinearMap.id)

/-- The alternating differential followed by the fold augmentation is zero.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
theorem simplexAugmentation_comp_differential_zero (Λ : Type u) [CommRing Λ] (m : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    ModuleCat.ofHom (simplexDifferential Λ m 0 M) ≫
        ModuleCat.ofHom (simplexAugmentation Λ m M) = 0 := by
  sorry

/-- Consecutive alternating differentials compose to zero.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution). -/
theorem simplexDifferential_comp_zero (Λ : Type u) [CommRing Λ] (m p : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    ModuleCat.ofHom (simplexDifferential Λ m (p + 1) M) ≫
        ModuleCat.ofHom (simplexDifferential Λ m p M) = 0 := by
  sorry

/-- Exactness of the displayed augmented simplex complex.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C, componentwise
complex and vertex-zero extra-degeneracy contraction (blueprint:
lem-trf-total-site-simplex-free-resolution). -/
def simplexAugmentedExact (Λ : Type u) [CommRing Λ] (m : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] : Prop :=
  ShortComplex.Exact
      (ShortComplex.mk (ModuleCat.ofHom (simplexDifferential Λ m 0 M))
        (ModuleCat.ofHom (simplexAugmentation Λ m M))
        (simplexAugmentation_comp_differential_zero Λ m M)) ∧
    ∀ p : ℕ,
      ShortComplex.Exact
        (ShortComplex.mk (ModuleCat.ofHom (simplexDifferential Λ m (p + 1) M))
          (ModuleCat.ofHom (simplexDifferential Λ m p M))
          (simplexDifferential_comp_zero Λ m p M))

/-- For every `m ≥ 0` and every ordinary `Λ`-module `M`, the augmented complex
`⋯ → C₂(m,M) → C₁(m,M) → C₀(m,M) → M → 0`, with alternating face
maps and fold augmentation, is exact.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D7C
(blueprint: lem-trf-total-site-simplex-free-resolution).

Proof (postponed): the simplicial face identities give `d² = 0`. Prepending the
vertex `0` to a monotone simplex defines an extra-degeneracy contraction,
including the degree `-1` augmentation term. Thus the contraction identity
identifies every cycle with a boundary and the fold is surjective, with no
flatness, freeness, or finiteness assumption on `M`. -/
theorem totalSiteSimplexFreeResolution (Λ : Type u) [CommRing Λ] (m : ℕ)
    (M : Type v) [AddCommGroup M] [Module Λ M] :
    simplexAugmentedExact Λ m M := by
  sorry

end CategoryTheory
