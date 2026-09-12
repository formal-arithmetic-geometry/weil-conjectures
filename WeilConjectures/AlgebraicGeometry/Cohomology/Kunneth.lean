/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The Künneth formula in degree one

Let `X` and `Y` be proper varieties over an algebraically closed field `k`, with rational
points `x₀ ∈ X(k)` and `y₀ ∈ Y(k)`. The two slice inclusions
`j_{y₀} : X ⟶ X × Y` and `j_{x₀} : Y ⟶ X × Y` of
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral` restrict a cohomology class
on the product to the two factors, and the Künneth formula in degree one says that the two
restrictions together

`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)`, `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`

are an isomorphism of `k`-vector spaces. Only injectivity is used downstream — it is what makes
a line bundle on a product trivial as soon as it is trivial on the two slices — but the
statement is recorded in the form the blueprint gives it.

The restriction maps are defined in every degree, by
`AlgebraicGeometry.Scheme.Modules.H.structurePullbackMapOver`: the pullback comparison map on
the cohomology of a sheaf of modules, followed by the identification `f^* 𝒪_Y ≅ 𝒪_X`, which is
`k`-linear for a morphism of `k`-schemes.

## Main definitions

- `AlgebraicGeometry.kunnethMap` — the map `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`, as a `k`-linear map
  `H^n(X × Y, 𝒪) ⟶ H^n(X, 𝒪) ⊕ H^n(Y, 𝒪)` in every degree `n`.
- `AlgebraicGeometry.kunnethLinearEquivOne` — the degree-one Künneth map packaged as a
  `k`-linear isomorphism.

## Main statements

- `AlgebraicGeometry.bijective_kunnethMap_one` (blueprint: `prop:cube-kunneth-h1`) — **the
  Künneth formula in degree one**: for proper varieties `X` and `Y` over an algebraically
  closed field, the two slice restrictions together are a bijection
  `H¹(X × Y, 𝒪) ≃ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)`. This is `sorry` by design; see the implementation
  notes.
- `AlgebraicGeometry.injective_kunnethMap_one` — the injectivity, which is the half that is
  consumed downstream.

## Implementation notes

* `AlgebraicGeometry.bijective_kunnethMap_one` is `sorry` **by design**: it is the open
  obligation attached to `prop:cube-kunneth-h1` in the blueprint. Mathlib has neither the
  Künneth formula nor the coherence theorems that the usual proof of it rests on, so the
  chapter isolates it as an input and this file only states it. The map itself is *not*
  sorried: it is the honest composite of the pullback comparison maps, so a later proof has
  nothing to re-define.
* The product `X × Y` is `CategoryTheory.Limits.pullback` of the two structure morphisms, made
  a `k`-scheme by `AlgebraicGeometry.Scheme.overPullback`; that instance is scoped, so the file
  opens `AlgebraicGeometry.OverPullback`, and so must any consumer of these statements. The two
  slice inclusions are morphisms of `k`-schemes, which is what makes the restriction maps
  `k`-linear.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open OverPullback

section Kunneth

variable {k : Type u} [Field k]

variable (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ X ↘ Spec (.of k) = 𝟙 _)
  (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ Y ↘ Spec (.of k) = 𝟙 _)

/-- The Künneth map: restriction of a cohomology class on `X × Y` to the two slices
`X × {y₀}` and `{x₀} × Y`, as a `k`-linear map
`H^n(X × Y, 𝒪) ⟶ H^n(X, 𝒪) ⊕ H^n(Y, 𝒪)`. -/
noncomputable def kunnethMap (n : ℕ) :
    (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).structureModules.H n →ₗ[k]
      X.structureModules.H n × Y.structureModules.H n :=
  (Scheme.Modules.H.structurePullbackMapOver
      (sliceInclusionFst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) y₀ hy₀) k n).prod
    (Scheme.Modules.H.structurePullbackMapOver
      (sliceInclusionSnd (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) x₀ hx₀) k n)

@[simp]
lemma kunnethMap_fst (n : ℕ)
    (α : (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).structureModules.H n) :
    (kunnethMap X Y x₀ hx₀ y₀ hy₀ n α).1 =
      Scheme.Modules.H.structurePullbackMapOver
        (sliceInclusionFst (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) y₀ hy₀) k n α :=
  rfl

@[simp]
lemma kunnethMap_snd (n : ℕ)
    (α : (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).structureModules.H n) :
    (kunnethMap X Y x₀ hx₀ y₀ hy₀ n α).2 =
      Scheme.Modules.H.structurePullbackMapOver
        (sliceInclusionSnd (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) x₀ hx₀) k n α :=
  rfl

variable [IsAlgClosed k]
  [IsVariety (X ↘ Spec (.of k))] [IsVariety (Y ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]

/-- **The Künneth formula in degree one** (blueprint: `prop:cube-kunneth-h1`). For proper
varieties `X` and `Y` over an algebraically closed field `k` and rational points `x₀ ∈ X(k)`,
`y₀ ∈ Y(k)`, the two slice restrictions together

`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)`, `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`,

are a bijection, hence an isomorphism of `k`-vector spaces
(`AlgebraicGeometry.kunnethLinearEquivOne`).

The statement is true over an arbitrary field; `k` is assumed algebraically closed only
because the proof needs `H⁰(X, 𝒪_X) = k`, which Mathlib has in that case only
(`lem:cube-global-sections`). The hypothesis can be dropped once the general form
`lem:cube-global-sections-general` is available.

This is `sorry` **by design**: it is the open obligation of `prop:cube-kunneth-h1`. See the
implementation notes of this file. -/
theorem bijective_kunnethMap_one :
    Function.Bijective (kunnethMap X Y x₀ hx₀ y₀ hy₀ 1) :=
  sorry

/-- The half of the Künneth formula in degree one that is consumed downstream: a class on
`X × Y` vanishing on both slices vanishes. -/
theorem injective_kunnethMap_one :
    Function.Injective (kunnethMap X Y x₀ hx₀ y₀ hy₀ 1) :=
  (bijective_kunnethMap_one X Y x₀ hx₀ y₀ hy₀).injective

/-- The Künneth formula in degree one, as an isomorphism of `k`-vector spaces
`H¹(X × Y, 𝒪) ≃ H¹(X, 𝒪) ⊕ H¹(Y, 𝒪)`. -/
noncomputable def kunnethLinearEquivOne :
    (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).structureModules.H 1 ≃ₗ[k]
      X.structureModules.H 1 × Y.structureModules.H 1 :=
  LinearEquiv.ofBijective (kunnethMap X Y x₀ hx₀ y₀ hy₀ 1)
    (bijective_kunnethMap_one X Y x₀ hx₀ y₀ hy₀)

end Kunneth

end AlgebraicGeometry
