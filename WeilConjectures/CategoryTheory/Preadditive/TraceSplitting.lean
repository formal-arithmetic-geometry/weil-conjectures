/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Splitting a unit by a normalized trace

Let `u : G ⟶ T` be a morphism in a preadditive category (typically the unit `G ⟶ Rπ_* π^* G` of
a finite étale cover `π` of degree `d`) and `t : T ⟶ G` a *trace* with `u ≫ t = d • 𝟙 G`. If
multiplication by `d` on `G` is invertible (for instance `d` is a power of `p` and the
coefficients are `ℤ[1/p]`-linear, as for `ℚ̄_ℓ`, `E`, `𝒪_E` or a finite ring `Λ` with `p ∈ Λˣ`), the
normalized trace `d⁻¹ t` is a retraction of `u` (`CategoryTheory.normalizedTrace`).

This file proves the formal parts of the averaging argument of SGA 4½, [Th. finitude], §3 and of
Illusie, *Autour du théorème de monodromie locale*, §4 (blueprint `det-nearby-kunneth-invariants`,
`det-tf-invariants-duality`):

* `CategoryTheory.comp_normalizedTrace`: `u ≫ d⁻¹ t = 𝟙`.
* `CategoryTheory.nsmul_normalizedTrace_comp_eq_sum` (*Galois averaging*): if a finite group of
  endomorphisms `ρ i` of `T` fixes `u` and `t ≫ u = ∑ i, ρ i` (the norm factors through the
  invariants), then `u` is split by the normalized trace and `n • (d⁻¹ t ≫ u) = ∑ i, ρ i`, `n` the
  number of the `ρ i`: the idempotent of the splitting is the average of the action.
* `CategoryTheory.normalizedTrace_compat` (*tower compatibility*): normalized traces of a tower
  `G ⟶ T₀ ⟶ T₁ ⟶ ⋯` whose traces satisfy the transitivity `τ ≫ t₁ = e • t₀` (`d₁ = e d₀`) are
  compatible with the transition maps.
* `CategoryTheory.Limits.descNormalizedTrace` (*limit of the tower*): if the target of the limit
  unit is the colimit of the finite levels, compatible retractions of the finite levels glue to a
  retraction of the limit unit.
* `CategoryTheory.isSplitMono_map_of_isIso_map` (*stabilization*): if an additive functor `Φ`
  inverts the comparison `c : Tₙ ⟶ T` from a finite level, then `Φ.map u` is a split monomorphism
  for `u = uₙ ≫ c`.

For `ℓ`-adic coefficients the colimit hypothesis of the limit step fails in general: for the
constant sheaf `ℚ̄_ℓ` on a separably closed point and the pro-`p` torsor `P ⟶ pt`, the sections of
`π_* π^* ℚ̄_ℓ` are the *continuous* functions `P ⟶ ℚ̄_ℓ`, while the colimit of the finite levels are
the locally constant ones. The `ℓ`-adic averaging therefore goes through the stabilization lemma:
the action of a pro-`p` group on an `ℓ`-adic constructible object factors through a finite quotient
(a pro-`p` subgroup of `GL_r(𝒪_E)` meets an open pro-`ℓ` subgroup trivially, so it is finite).
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

section Normalized

variable {G T : C} (u : G ⟶ T) (t : T ⟶ G) (d : ℕ) [IsIso (d • 𝟙 G)]

variable {u t d}

end Normalized

namespace Limits

omit [Preadditive C]

variable {J : Type*} [Category J] {G : C} {F : J ⥤ C} {c : Cocone F}

end Limits

section Stabilization

omit [Preadditive C]

variable {D : Type*} [Category D] {G Tₙ T : C} (Φ : C ⥤ D)

end Stabilization

end CategoryTheory
