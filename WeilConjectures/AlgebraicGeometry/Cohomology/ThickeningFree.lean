/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Cohomology.Thickening
public import WeilConjectures.AlgebraicGeometry.ThickeningFree

/-!
# The cohomology of a free infinitesimal thickening ideal

Let `f : W ⟶ T` be a morphism of schemes, let `t` be a point of `T`, write
`Wₘ := W ×_T Tₘ` for the base change of `f` along the `m`-th infinitesimal neighbourhood of
`t`, let `Iₙ` be the thickening ideal of `Wₙ ↪ W_{n+1}` and let
`i₀ : W₀ ↪ W_{n+1}` be the closed immersion of the zeroth infinitesimal neighbourhood.

A finite family `m : ι → Γ(Iₙ, ⊤)` of global sections of the thickening ideal gives the
comparison morphism `Φ : (i₀)_* (𝒪_{W₀} ^ ι) ⟶ Iₙ` of
`AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal`. **Whenever `Φ` is an
isomorphism** — which happens when `f` is flat and the `m j` are the images of a `κ(t)`-basis
of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`, by
`AlgebraicGeometry.Scheme.isIso_pushforwardFreeToThickeningIdeal` — the cohomology of the
thickening ideal is an `ι`-fold power of the cohomology of the structure sheaf of the zeroth
neighbourhood:

`H^k(W_{n+1}, Iₙ) ≅ (ι → H^k(W₀, 𝒪_{W₀}))`.

This file assembles that identification out of three steps:

1. `H^k(W_{n+1}, Iₙ) ≅ H^k(W_{n+1}, (i₀)_* (𝒪_{W₀} ^ ι))`, the isomorphism `Φ` on
   cohomology (`AlgebraicGeometry.Scheme.Modules.H.mapLinearEquiv`);
2. `H^k(W_{n+1}, (i₀)_* (𝒪_{W₀} ^ ι)) ≅ H^k(W₀, 𝒪_{W₀} ^ ι)`, cohomology is invariant under
   pushforward along a closed immersion
   (`AlgebraicGeometry.Scheme.Modules.H.pushforwardAddEquiv`);
3. `H^k(W₀, 𝒪_{W₀} ^ ι) ≅ (ι → H^k(W₀, 𝒪_{W₀}))`, cohomology commutes with finite direct
   sums (`AlgebraicGeometry.Scheme.Modules.H.freeLinearEquiv`).

Step 2 is only semilinear over `i₀.appTop : Γ(W_{n+1}, 𝒪) ⟶ Γ(W₀, 𝒪)`, so the composite is
stated first as an isomorphism of additive groups; it is linear over a base ring `R` as soon
as `W₀` and `W_{n+1}` are schemes over `Spec R` and `i₀` is a morphism over `Spec R`.

For the induction of `lem:cube-thickening-trivial` the identification is used on the group
`H¹(W_{n+1}, Iₙ)` of deformation classes, which is written multiplicatively there; the
multiplicative form is `AlgebraicGeometry.Scheme.thickeningH1FreeMulEquiv`.

## Main definitions

- `AlgebraicGeometry.Scheme.thickeningH1FreeAddEquiv` — the identification
  `H^k(W_{n+1}, Iₙ) ≃+ (ι → H^k(W₀, 𝒪_{W₀}))`.
- `AlgebraicGeometry.Scheme.thickeningH1FreeLinearEquiv` — the same identification as an
  `R`-linear isomorphism, for schemes over `Spec R`.
- `AlgebraicGeometry.Scheme.thickeningH1FreeMulEquiv` — the same identification between the
  multiplicative versions of the two groups, the form in which
  `AlgebraicGeometry.Scheme.thickeningH1Map` takes its values.

## Naturality

The naturality of this identification in a morphism `u : W' ⟶ W` over `T` — the square
relating it to `AlgebraicGeometry.Scheme.thickeningH1Map` — is not proved here: it needs the
compatibility of the two isomorphisms of steps 1 and 2 with the pullback map on cohomology
along the base change of `u`, and for step 2 no such compatibility is available (the
pushforward isomorphism comes from an adjunction and the pullback map from
`CategoryTheory.Abelian.Ext.mapExactFunctor`, which Mathlib does not know to be functorial
in the exact functor; compare the TODO of
`WeilConjectures.AlgebraicGeometry.Cohomology.Pullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ) {ι : Type u} [Fintype ι]
  (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
  [IsIso (pushforwardFreeToThickeningIdeal f t n m)] (k : ℕ)

/-- **The cohomology of a free thickening ideal is a finite power of the cohomology of the
structure sheaf of the zeroth infinitesimal neighbourhood**:
`H^k(W ×_T T_{n+1}, Iₙ) ≃+ (ι → H^k(W ×_T T₀, 𝒪))`, under the assumption that the comparison
morphism `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` attached to the family
`m` of global sections of `Iₙ` is an isomorphism.

The `R`-linear form for schemes over `Spec R` is
`AlgebraicGeometry.Scheme.thickeningH1FreeLinearEquiv`. -/
noncomputable def thickeningH1FreeAddEquiv :
    (thickeningIdeal f t n).toModules.H k ≃+
      (ι → (infinitesimalBaseChange f t 0).structureModules.H k) :=
  (Modules.H.mapLinearEquiv
        (asIso (pushforwardFreeToThickeningIdeal f t n m)) k).symm.toAddEquiv.trans
    (((Modules.H.pushforwardAddEquiv (infinitesimalBaseChangeMapZero f t n)
          ((infinitesimalBaseChange f t 0).freeModules ι) k).symm).trans
      (Modules.H.freeLinearEquiv (infinitesimalBaseChange f t 0) ι k).toAddEquiv)

lemma thickeningH1FreeAddEquiv_apply (x : (thickeningIdeal f t n).toModules.H k) :
    thickeningH1FreeAddEquiv f t n m k x =
      Modules.H.freeLinearEquiv (infinitesimalBaseChange f t 0) ι k
        (Modules.H.pushforwardMap (infinitesimalBaseChangeMapZero f t n)
          ((infinitesimalBaseChange f t 0).freeModules ι) k
          (Modules.H.map (asIso (pushforwardFreeToThickeningIdeal f t n m)).inv k x)) :=
  rfl

lemma thickeningH1FreeAddEquiv_symm_apply
    (p : ι → (infinitesimalBaseChange f t 0).structureModules.H k) :
    (thickeningH1FreeAddEquiv f t n m k).symm p =
      Modules.H.map (pushforwardFreeToThickeningIdeal f t n m) k
        (Modules.H.pushforwardAddEquiv (infinitesimalBaseChangeMapZero f t n)
          ((infinitesimalBaseChange f t 0).freeModules ι) k
          ((Modules.H.freeLinearEquiv (infinitesimalBaseChange f t 0) ι k).symm p)) :=
  rfl

/-- **The cohomology of a free thickening ideal, multiplicatively**:
`H^k(W ×_T T_{n+1}, Iₙ) ≃* (ι → H^k(W ×_T T₀, 𝒪))` for the multiplicative versions of the two
groups. This is the form in which `AlgebraicGeometry.Scheme.thickeningH1Map`, hence the
Künneth hypothesis of `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one`,
sees the group of deformation classes. -/
noncomputable def thickeningH1FreeMulEquiv :
    Multiplicative ((thickeningIdeal f t n).toModules.H k) ≃*
      Multiplicative (ι → (infinitesimalBaseChange f t 0).structureModules.H k) :=
  AddEquiv.toMultiplicative (thickeningH1FreeAddEquiv f t n m k)

lemma thickeningH1FreeMulEquiv_apply
    (x : Multiplicative ((thickeningIdeal f t n).toModules.H k)) :
    thickeningH1FreeMulEquiv f t n m k x =
      Multiplicative.ofAdd
        (thickeningH1FreeAddEquiv f t n m k (Multiplicative.toAdd x)) :=
  rfl

/-! ### Schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R]
  [(infinitesimalBaseChange f t (n + 1)).Over (Spec (.of R))]
  [(infinitesimalBaseChange f t 0).Over (Spec (.of R))]
  [(infinitesimalBaseChangeMapZero f t n).IsOver (Spec (.of R))]

/-- **The cohomology of a free thickening ideal is a finite power of the cohomology of the
structure sheaf of the zeroth infinitesimal neighbourhood**, `R`-linearly for schemes over
`Spec R`: `H^k(W ×_T T_{n+1}, Iₙ) ≃ₗ[R] (ι → H^k(W ×_T T₀, 𝒪))`. For `R` a field this is an
isomorphism of `R`-vector spaces, and the blueprint's identification of `H¹` of the
thickening ideal with `H¹(W, 𝒪_W) ⊗_R Iₙ` once a basis of `Iₙ` over `R` is chosen. -/
noncomputable def thickeningH1FreeLinearEquiv :
    (thickeningIdeal f t n).toModules.H k ≃ₗ[R]
      (ι → (infinitesimalBaseChange f t 0).structureModules.H k) :=
  (Modules.H.mapLinearEquivOver R
        (asIso (pushforwardFreeToThickeningIdeal f t n m)) k).symm.trans
    ((AddEquiv.toLinearEquiv
        (Modules.H.pushforwardAddEquiv (infinitesimalBaseChangeMapZero f t n)
          ((infinitesimalBaseChange f t 0).freeModules ι) k).symm
        (fun r y ↦ by
          simpa using Modules.H.pushforwardMap_smul_over
            (infinitesimalBaseChangeMapZero f t n)
            ((infinitesimalBaseChange f t 0).freeModules ι) k R r y)).trans
      (Modules.H.freeLinearEquivOver R (infinitesimalBaseChange f t 0) ι k))

lemma thickeningH1FreeLinearEquiv_apply (x : (thickeningIdeal f t n).toModules.H k) :
    thickeningH1FreeLinearEquiv f t n m k R x = thickeningH1FreeAddEquiv f t n m k x :=
  rfl

end OverBase

end AlgebraicGeometry.Scheme
