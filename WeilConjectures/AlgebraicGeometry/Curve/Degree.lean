/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# The degree of an effective Cartier divisor

Let `X` be a scheme over a field `k` and let `z : D ⟶ X` be an effective Cartier divisor, i.e.
an effective Cartier centre (`AlgebraicGeometry.IsEffectiveCartierCenter`). When `D` is finite
over `k`, as it is on a proper curve, its degree is `deg D = dim_k Γ(D, 𝒪_D)`. For
`D = ∑_x n_x x` on a curve, `Γ(D, 𝒪_D) = ∏_x 𝒪_{X,x}/𝔪_x^{n_x}` has dimension
`∑_x n_x [κ(x) : k]`, which is the classical degree of a divisor.

A line bundle `ℒ` is *the twist `𝒪_X(D)`* when the ideal sheaf `𝒪_X(-D)` of `D`, the kernel of
`𝒪_X ⟶ z_* 𝒪_D`, is the image of a monomorphism from the dual `ℒᵛ`. There is no twisting sheaf
`𝒪_X(D)` in Mathlib, so this is recorded as the predicate
`AlgebraicGeometry.Scheme.Modules.IsEffectiveCartierTwist`.

## Main definitions

- `AlgebraicGeometry.Scheme.effectiveCartierDegree`: the degree `dim_k Γ(D, 𝒪_D)` of an
  effective Cartier divisor `z : D ⟶ X`.
- `AlgebraicGeometry.Scheme.Modules.IsEffectiveCartierTwist`: the module `ℒ` is `𝒪_X(D)` for
  the effective Cartier divisor `z : D ⟶ X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X D : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `dim_k Γ(D, 𝒪_D)` of an effective Cartier divisor `z : D ⟶ X` on a
`k`-scheme `X`, where `Γ(D, 𝒪_D)` is a `k`-vector space through `k → Γ(X, 𝒪_X) → Γ(D, 𝒪_D)`.

For `D = ∑_x n_x x` finite over `k`, this is `∑_x n_x [κ(x) : k]`. The definition makes sense
for any morphism `z`, but is the degree of a divisor only when `z` is an effective Cartier centre
with `D` finite over `k`; when `Γ(D, 𝒪_D)` is infinite-dimensional the value is `0`.

(blueprint: `sk-thm-picard-rr`) -/
noncomputable def effectiveCartierDegree (z : D ⟶ X) : ℕ :=
  letI : Module k Γ(D, ⊤) :=
    Module.compHom _ (z.appTop.hom.comp (globalSectionsRingHom k (X := X)))
  Module.finrank k Γ(D, ⊤)

variable {k}

/-- The sheaf of modules `ℒ` on `X` is **the twist `𝒪_X(D)`** by the effective Cartier divisor
`z : D ⟶ X`: `z` is an effective Cartier centre and there is a monomorphism `s : ℒᵛ ⟶ 𝒪_X`
whose cokernel is `z_* 𝒪_D`. In other words, `s` identifies `ℒᵛ` with the ideal sheaf
`𝒪_X(-D)` of `D`, so that `ℒ ≅ 𝒪_X(D)` for invertible `ℒ`.

(blueprint: `sk-thm-picard-rr`) -/
def Modules.IsEffectiveCartierTwist (ℒ : X.Modules) (z : D ⟶ X) : Prop :=
  IsEffectiveCartierCenter z ∧
    ∃ s : ℒᵛ ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules), Mono s ∧
      Nonempty (cokernel s ≅ (Modules.pushforward z).obj (SheafOfModules.unit D.ringCatSheaf))

end AlgebraicGeometry.Scheme
