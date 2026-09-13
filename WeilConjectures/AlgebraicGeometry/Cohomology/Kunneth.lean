/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The Künneth formula in degree one

Let `X` and `Y` be proper varieties over a field `k`, with rational points `x₀ ∈ X(k)` and
`y₀ ∈ Y(k)`. The two slice inclusions `AlgebraicGeometry.sliceInclusionFst`
(`j_{y₀} : X ⟶ X × Y`) and `AlgebraicGeometry.sliceInclusionSnd` (`j_{x₀} : Y ⟶ X × Y`)
restrict a cohomology class on the product to the two factors, and the Künneth formula in
degree one says that the two restrictions together

`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) × H¹(Y, 𝒪)`, `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`

are an isomorphism of `k`-vector spaces. (The binary product of `k`-vector spaces is their
direct sum; the blueprint writes it `⊕`.) Only injectivity is used downstream, where
`lem:cube-thickening-trivial` applies it to a deformation class in `H¹(W, 𝒪_W) ⊗[k] I`, but
the statement is recorded in the form the blueprint gives it.

The restriction maps themselves need no field: they are defined for two schemes over
`Spec R` with sections, in every degree, by
`AlgebraicGeometry.Scheme.Modules.H.structurePullbackMapOver`: the pullback comparison map on
the cohomology of a sheaf of modules, followed by the identification `f^* 𝒪_Y ≅ 𝒪_X`, which is
`R`-linear for a morphism of `R`-schemes.

## Main definitions

- `AlgebraicGeometry.sliceRestrictionMap` — the map `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`, as an
  `R`-linear map `H^n(X × Y, 𝒪) ⟶ H^n(X, 𝒪) × H^n(Y, 𝒪)` in every degree `n`. It is the
  Künneth comparison map only in degree one, which is why it is not named after Künneth.
- `AlgebraicGeometry.kunnethLinearEquivOne` — the degree-one slice restriction packaged as a
  `k`-linear isomorphism.

## Main statements

- `AlgebraicGeometry.bijective_sliceRestrictionMap_one` (blueprint: `prop:cube-kunneth-h1`) —
  **the Künneth formula in degree one**: for proper varieties `X` and `Y` the two slice
  restrictions together are a bijection `H¹(X × Y, 𝒪) ≃ H¹(X, 𝒪) × H¹(Y, 𝒪)`. This is `sorry`
  by design; see the implementation notes.
- `AlgebraicGeometry.injective_sliceRestrictionMap_one` — the injectivity, which is the half
  that is consumed downstream.

## Implementation notes

* `AlgebraicGeometry.bijective_sliceRestrictionMap_one` is `sorry` **by design**: it is the
  open obligation attached to `prop:cube-kunneth-h1` in the blueprint. Mathlib has neither the
  Künneth formula nor the coherence theorems that the usual proof of it rests on, so the
  chapter isolates it as an input and this file only states it. The map itself is *not*
  sorried: it is the honest composite of the pullback comparison maps, so a later proof has
  nothing to re-define.
* The product `X × Y` is `CategoryTheory.Limits.pullback` of the two structure morphisms,
  a `k`-scheme through `AlgebraicGeometry.Scheme.canonicallyOverPullback`. The two slice
  inclusions are morphisms of `k`-schemes, which is what makes the restriction maps `k`-linear.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section BaseRing

variable {R : Type u} [CommRing R]

variable (X Y : Scheme.{u}) [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (x₀ : Spec (.of R) ⟶ X) (hx₀ : x₀ ≫ X ↘ Spec (.of R) = 𝟙 _)
  (y₀ : Spec (.of R) ⟶ Y) (hy₀ : y₀ ≫ Y ↘ Spec (.of R) = 𝟙 _)

/-- Restriction of a cohomology class on `X × Y` to the two slices `X × {y₀}` and `{x₀} × Y`,
as an `R`-linear map `H^n(X × Y, 𝒪) ⟶ H^n(X, 𝒪) × H^n(Y, 𝒪)`, for two schemes `X` and `Y`
over `Spec R` with sections `x₀` and `y₀`:

```
  X ──j_{y₀}──▶ X ×_R Y ◀──j_{x₀}── Y

  H^n(X, 𝒪) ◀──j_{y₀}^*── H^n(X ×_R Y, 𝒪) ──j_{x₀}^*──▶ H^n(Y, 𝒪)
```

In degree one it is the Künneth comparison map; see
`AlgebraicGeometry.bijective_sliceRestrictionMap_one`. -/
noncomputable def sliceRestrictionMap (n : ℕ) :
    (pullback (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))).structureModules.H n →ₗ[R]
      X.structureModules.H n × Y.structureModules.H n :=
  (Scheme.Modules.H.structurePullbackMapOver R
      (sliceInclusionFst (X ↘ Spec (.of R)) (Y ↘ Spec (.of R)) y₀ hy₀) n).prod
    (Scheme.Modules.H.structurePullbackMapOver R
      (sliceInclusionSnd (X ↘ Spec (.of R)) (Y ↘ Spec (.of R)) x₀ hx₀) n)

@[simp]
lemma sliceRestrictionMap_fst (n : ℕ)
    (α : (pullback (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))).structureModules.H n) :
    (sliceRestrictionMap X Y x₀ hx₀ y₀ hy₀ n α).1 =
      Scheme.Modules.H.structurePullbackMapOver R
        (sliceInclusionFst (X ↘ Spec (.of R)) (Y ↘ Spec (.of R)) y₀ hy₀) n α :=
  rfl

@[simp]
lemma sliceRestrictionMap_snd (n : ℕ)
    (α : (pullback (X ↘ Spec (.of R)) (Y ↘ Spec (.of R))).structureModules.H n) :
    (sliceRestrictionMap X Y x₀ hx₀ y₀ hy₀ n α).2 =
      Scheme.Modules.H.structurePullbackMapOver R
        (sliceInclusionSnd (X ↘ Spec (.of R)) (Y ↘ Spec (.of R)) x₀ hx₀) n α :=
  rfl

end BaseRing

section Field

variable {k : Type u} [Field k]

variable (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  (x₀ : Spec (.of k) ⟶ X) (hx₀ : x₀ ≫ X ↘ Spec (.of k) = 𝟙 _)
  (y₀ : Spec (.of k) ⟶ Y) (hy₀ : y₀ ≫ Y ↘ Spec (.of k) = 𝟙 _)
  [IsVariety (X ↘ Spec (.of k))] [IsVariety (Y ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]

/-- **The Künneth formula in degree one** (blueprint: `prop:cube-kunneth-h1`). For proper
varieties `X` and `Y` over a field `k` and rational points `x₀ ∈ X(k)`, `y₀ ∈ Y(k)`, the two
slice restrictions together

`H¹(X × Y, 𝒪) ⟶ H¹(X, 𝒪) × H¹(Y, 𝒪)`, `α ↦ (j_{y₀}^* α, j_{x₀}^* α)`,

are a bijection, hence an isomorphism of `k`-vector spaces
(`AlgebraicGeometry.kunnethLinearEquivOne`).

This is `sorry` **by design**: it is the open obligation of `prop:cube-kunneth-h1`. See the
implementation notes of this file. -/
theorem bijective_sliceRestrictionMap_one :
    Function.Bijective (sliceRestrictionMap X Y x₀ hx₀ y₀ hy₀ 1) :=
  sorry

/-- The half of the Künneth formula in degree one that is consumed downstream: a class on
`X × Y` vanishing on both slices vanishes. -/
theorem injective_sliceRestrictionMap_one :
    Function.Injective (sliceRestrictionMap X Y x₀ hx₀ y₀ hy₀ 1) :=
  (bijective_sliceRestrictionMap_one X Y x₀ hx₀ y₀ hy₀).injective

/-- The Künneth formula in degree one, as an isomorphism of `k`-vector spaces
`H¹(X × Y, 𝒪) ≃ H¹(X, 𝒪) × H¹(Y, 𝒪)`. -/
noncomputable def kunnethLinearEquivOne :
    (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).structureModules.H 1 ≃ₗ[k]
      X.structureModules.H 1 × Y.structureModules.H 1 :=
  LinearEquiv.ofBijective (sliceRestrictionMap X Y x₀ hx₀ y₀ hy₀ 1)
    (bijective_sliceRestrictionMap_one X Y x₀ hx₀ y₀ hy₀)

end Field

end AlgebraicGeometry
