/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Ext groups of sheaves of modules on a scheme

For `𝒪_X`-modules `ℱ` and `𝒢` on a scheme `X`, the group `Ext^i_X(ℱ, 𝒢)` is the `i`-th right
derived functor of `Hom_{𝒪_X}(-, 𝒢)` evaluated at `ℱ`. We use Mathlib's `Abelian.Ext`, the
morphisms `ℱ ⟶ 𝒢[i]` in the derived category of the abelian category `X.Modules`, which computes
these derived functors.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.Ext`: the group `Ext^i_X(ℱ, 𝒢)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.contravariantSequence_ext_exact`: the long exact sequence of
  `Ext(-, 𝒢)` attached to a short exact sequence.
- `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`: for finite locally free `ℱ`,
  `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`.

## Implementation notes

The `Ext` groups need the hypothesis `HasExt.{u} X.Modules`, which holds because `X.Modules` is a
Grothendieck abelian category (`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`); it is
kept as an instance argument.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [HasExt.{u} X.Modules]

/-- The **Ext groups** `Ext^i_X(ℱ, 𝒢)` of two `𝒪_X`-modules: the right derived functors of
`Hom_{𝒪_X}(-, 𝒢)` on the abelian category of `𝒪_X`-modules, evaluated at `ℱ`. In degree `0` this
is `Hom_{𝒪_X}(ℱ, 𝒢)` (`CategoryTheory.Abelian.Ext.homEquiv₀`).

(blueprint: `def-sc-ext-sheaf`) -/
abbrev Ext (ℱ 𝒢 : X.Modules) (i : ℕ) : Type u :=
  Abelian.Ext ℱ 𝒢 i

/-- **The long exact `Ext` sequence.** A short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of
`𝒪_X`-modules gives, for every `𝒢` and `1 + n₀ = n₁`, the exact sequence
`Ext^{n₀}(ℱ₃, 𝒢) → Ext^{n₀}(ℱ₂, 𝒢) → Ext^{n₀}(ℱ₁, 𝒢) → Ext^{n₁}(ℱ₃, 𝒢) → Ext^{n₁}(ℱ₂, 𝒢) →
Ext^{n₁}(ℱ₁, 𝒢)`. The comparison with sheaf cohomology for finite locally free `ℱ` is
`AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H`.

(blueprint: `rem-ptr-sc-ext-sheaf-4`) -/
theorem contravariantSequence_ext_exact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (𝒢 : X.Modules) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Abelian.Ext.contravariantSequence hS 𝒢 n₀ n₁ h).Exact :=
  Abelian.Ext.contravariantSequence_exact hS 𝒢 n₀ n₁ h

/-- **Ext of a finite locally free module.** For a finite locally free `𝒪_X`-module `ℱ` and any
`𝒪_X`-module `𝒢`, `Ext^i_X(ℱ, 𝒢) ≅ H^i(X, ℱᵛ ⊗ 𝒢)`. Indeed `Hom(ℱ, -) = Γ(X, ℱᵛ ⊗ -)` is the
composite of the exact functor `ℱᵛ ⊗ -` with `Γ(X, -)`. In particular
`Ext^i_X(𝒪_X, 𝒢) = H^i(X, 𝒢)`.

(blueprint: `lem-sc-ext-locally-free`) -/
theorem nonempty_ext_addEquiv_H (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteLocallyFree] (i : ℕ) :
    Nonempty (Ext ℱ 𝒢 i ≃+ (ℱᵛ ⊗ 𝒢).H i) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
