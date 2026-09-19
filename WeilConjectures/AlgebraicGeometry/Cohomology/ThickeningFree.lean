/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ClosedImmersion
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
isomorphism** — which happens when the `m j` are the images of a `κ(t)`-basis of
`𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`, and which is *not* proved here — the cohomology of the
thickening ideal is an `ι`-fold power of the cohomology of the structure sheaf of the zeroth
neighbourhood:

```
  H^d(W_{n+1}, (i₀)_* (𝒪_{W₀} ^ ι)) ────H^d(Φ)────▶ H^d(W_{n+1}, Iₙ)
                            ╲                              │
  H.pushforwardFreeAddEquiv  ╲                             │ thickeningIdealHFreeAddEquiv
                              ╲                            ▼
                               ╲─────────────────────────▶ (ι → H^d(W₀, 𝒪_{W₀}))
```

The slanted arrow is `AlgebraicGeometry.Scheme.Modules.H.pushforwardFreeAddEquiv`, which is
where all the work happens: cohomology is invariant under pushforward along a closed
immersion and commutes with finite direct sums. Nothing about thickenings enters there, so
this file only specialises it along `H^d(Φ)`.

The isomorphism `H^d(Φ)` is `Γ(W_{n+1}, 𝒪)`-linear while the slanted arrow is only
semilinear over `i₀.appTop : Γ(W_{n+1}, 𝒪) ⟶ Γ(W₀, 𝒪)`, so the composite is stated first as
an isomorphism of additive groups, with its semilinearity recorded separately; it is linear
over a base ring `R` as soon as `W₀` and `W_{n+1}` are schemes over `Spec R` and `i₀` is a
morphism over `Spec R`.

The index type `ι` is in the same universe `u` as the schemes, because that is the
generality in which cohomology is known here to commute with finite direct sums
(`AlgebraicGeometry.Scheme.Modules.H.freeLinearEquiv`).

## Main definitions

- `AlgebraicGeometry.Scheme.thickeningIdealHFreeAddEquiv` — the identification
  `H^d(W_{n+1}, Iₙ) ≃+ (ι → H^d(W₀, 𝒪_{W₀}))`.
- `AlgebraicGeometry.Scheme.thickeningIdealHFreeLinearEquiv` — the same identification as an
  `R`-linear isomorphism, for schemes over `Spec R`.

## TODO

Prove the naturality of this identification in a morphism `u : W' ⟶ W` over `T`, that is, the
square relating it to `AlgebraicGeometry.Scheme.thickeningH1Map`, which is what the induction
of `lem:cube-thickening-trivial` needs of it. This requires the compatibility of `H^d(Φ)` and
of `AlgebraicGeometry.Scheme.Modules.H.pushforwardFreeAddEquiv` with the pullback map on
cohomology along the base change of `u`, and for the latter no such compatibility is
available (the pushforward isomorphism comes from an adjunction and the pullback map from
`CategoryTheory.Abelian.Ext.mapExactFunctor`, which Mathlib does not know to be functorial in
the exact functor; compare the TODO of
`WeilConjectures.AlgebraicGeometry.Cohomology.Pullback`). It also requires relating the
family `m` on `W` to a family on `W'`, which is not done here either.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

section

variable {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ) {ι : Type u} [Fintype ι]
  (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
  [IsIso (pushforwardFreeToThickeningIdeal f t n m)] (d : ℕ)

/-- **The cohomology of a free thickening ideal is a finite power of the cohomology of the
structure sheaf of the zeroth infinitesimal neighbourhood**:
`H^d(W ×_T T_{n+1}, Iₙ) ≃+ (ι → H^d(W ×_T T₀, 𝒪))`, under the assumption that the comparison
morphism `Φ = AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` attached to the
family `m` of global sections of `Iₙ` is an isomorphism.

```
  H^d(W ×_T T_{n+1}, (i₀)_* (𝒪 ^ ι)) ────H^d(Φ)────▶ H^d(W ×_T T_{n+1}, Iₙ)
                             ╲                               │
  H.pushforwardFreeAddEquiv   ╲                              │ this equivalence
                               ╲                             ▼
                                ╲─────────────────────────▶ (ι → H^d(W ×_T T₀, 𝒪))
```

No instance can discharge `IsIso Φ`, since the family `m` is arbitrary data; supply it with
`haveI`, as one does for `CategoryTheory.asIso`.

The `R`-linear form for schemes over `Spec R` is
`AlgebraicGeometry.Scheme.thickeningIdealHFreeLinearEquiv`. -/
noncomputable def thickeningIdealHFreeAddEquiv :
    (thickeningIdeal f t n).toModules.H d ≃+
      (ι → (infinitesimalBaseChange f t 0).structureModules.H d) :=
  (Modules.H.mapLinearEquiv
        (asIso (pushforwardFreeToThickeningIdeal f t n m)) d).symm.toAddEquiv.trans
    (Modules.H.pushforwardFreeAddEquiv (infinitesimalBaseChangeMapZero f t n) ι d)

lemma thickeningIdealHFreeAddEquiv_apply (x : (thickeningIdeal f t n).toModules.H d) :
    thickeningIdealHFreeAddEquiv f t n m d x =
      Modules.H.pushforwardFreeAddEquiv (infinitesimalBaseChangeMapZero f t n) ι d
        (Modules.H.map (asIso (pushforwardFreeToThickeningIdeal f t n m)).inv d x) :=
  rfl

lemma thickeningIdealHFreeAddEquiv_symm_apply
    (p : ι → (infinitesimalBaseChange f t 0).structureModules.H d) :
    (thickeningIdealHFreeAddEquiv f t n m d).symm p =
      Modules.H.map (pushforwardFreeToThickeningIdeal f t n m) d
        ((Modules.H.pushforwardFreeAddEquiv (infinitesimalBaseChangeMapZero f t n) ι d).symm
          p) :=
  rfl

/-- `H^d(W ×_T T_{n+1}, Iₙ) ≃+ (ι → H^d(W ×_T T₀, 𝒪))` is semilinear over
`i₀.appTop : Γ(W ×_T T_{n+1}, 𝒪) ⟶ Γ(W ×_T T₀, 𝒪)`. -/
lemma thickeningIdealHFreeAddEquiv_smul (r : Γ(infinitesimalBaseChange f t (n + 1), ⊤))
    (x : (thickeningIdeal f t n).toModules.H d) :
    thickeningIdealHFreeAddEquiv f t n m d (r • x) =
      (infinitesimalBaseChangeMapZero f t n).appTop.hom r •
        thickeningIdealHFreeAddEquiv f t n m d x := by
  rw [thickeningIdealHFreeAddEquiv_apply, thickeningIdealHFreeAddEquiv_apply,
    (Modules.H.map (asIso (pushforwardFreeToThickeningIdeal f t n m)).inv d).map_smul r x,
    Modules.H.pushforwardFreeAddEquiv_smul]

end

/-! ### Schemes over a base ring -/

section OverBase

variable (R : Type u) [CommRing R] {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ)
  {ι : Type u} [Fintype ι] (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
  [IsIso (pushforwardFreeToThickeningIdeal f t n m)]
  [(infinitesimalBaseChange f t (n + 1)).Over (Spec (.of R))]
  [(infinitesimalBaseChange f t 0).Over (Spec (.of R))]
  [(infinitesimalBaseChangeMapZero f t n).IsOver (Spec (.of R))] (d : ℕ)

/-- **The cohomology of a free thickening ideal is a finite power of the cohomology of the
structure sheaf of the zeroth infinitesimal neighbourhood**, `R`-linearly for schemes over
`Spec R`: `H^d(W ×_T T_{n+1}, Iₙ) ≃ₗ[R] (ι → H^d(W ×_T T₀, 𝒪))`.

For `R` a field and `ι` indexing a `κ(t)`-basis of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)` this is
the blueprint's identification of `H¹` of the thickening ideal with `H¹(W, 𝒪_W) ⊗_R Iₙ` in
`lem:cube-thickening-trivial`, up to two differences: the right-hand side here is the
cohomology of the zeroth infinitesimal neighbourhood `W ×_T T₀` rather than of `W`, and the
tensor product is replaced by an `ι`-fold power. That `Φ` is an isomorphism for such a family
`m` is not proved here. -/
noncomputable def thickeningIdealHFreeLinearEquiv :
    (thickeningIdeal f t n).toModules.H d ≃ₗ[R]
      (ι → (infinitesimalBaseChange f t 0).structureModules.H d) :=
  (Modules.H.mapLinearEquivOver R
        (asIso (pushforwardFreeToThickeningIdeal f t n m)) d).symm.trans
    (Modules.H.pushforwardFreeLinearEquivOver R (infinitesimalBaseChangeMapZero f t n) ι d)

@[simp]
lemma thickeningIdealHFreeLinearEquiv_apply (x : (thickeningIdeal f t n).toModules.H d) :
    thickeningIdealHFreeLinearEquiv R f t n m d x = thickeningIdealHFreeAddEquiv f t n m d x :=
  rfl

@[simp]
lemma thickeningIdealHFreeLinearEquiv_symm_apply
    (p : ι → (infinitesimalBaseChange f t 0).structureModules.H d) :
    (thickeningIdealHFreeLinearEquiv R f t n m d).symm p =
      (thickeningIdealHFreeAddEquiv f t n m d).symm p :=
  rfl

end OverBase

end AlgebraicGeometry.Scheme
