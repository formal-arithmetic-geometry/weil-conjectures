/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ClosedImmersionBaseChange
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

## Naturality in the scheme

A morphism `u : W' ⟶ W` over `T` base changes to `W' ×_T Tₘ ⟶ W ×_T Tₘ` for every `m`, and the
identification is natural for it: the last section of this file proves that it intertwines
`AlgebraicGeometry.Scheme.thickeningH1Map` with the `ι`-fold power of the pullback map on `H^k`
of the structure sheaf of the zeroth neighbourhood.

Each of the three steps above is natural — steps 1 and 3 through
`AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_map` and step 2 through
`AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom_pushforwardAddEquiv`, base change for
cohomology along a closed immersion — and the three are composed in
`AlgebraicGeometry.Scheme.Modules.H.map_pullbackAddHom_pushforwardAddEquiv_freeLinearEquiv_symm`.

One hypothesis is needed, because the identification depends on a datum that `u` does not
determine: the comparison morphisms `Φ` on `W` and `Φ'` on `W'` are attached to two families
`m` and `m'` of global sections chosen independently, so they have to be assumed compatible
across the base change. That hypothesis is
`AlgebraicGeometry.Scheme.PushforwardFreeToThickeningIdealBaseChange`.

## Main statements

- `AlgebraicGeometry.Scheme.thickeningH1FreeAddEquiv_naturality` — the identification is natural
  in the scheme.
- `AlgebraicGeometry.Scheme.toAdd_thickeningH1FreeMulEquiv_thickeningH1Map` — the same square
  for `AlgebraicGeometry.Scheme.thickeningH1Map`, in multiplicative form.
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

namespace AlgebraicGeometry.Scheme

/-! ### Naturality in the scheme -/

variable {T W W' : Scheme.{u}} (f : W ⟶ T) (f' : W' ⟶ T) (u : W' ⟶ W) (hu : u ≫ f = f')
  (t : T) (n : ℕ) {ι : Type u} [Fintype ι]
  (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
  (m' : ι → Γ((thickeningIdeal f' t n).toModules, ⊤))
  [IsIso (pushforwardFreeToThickeningIdeal f t n m)]
  [IsIso (pushforwardFreeToThickeningIdeal f' t n m')]
  (k : ℕ)

/-- **The comparison morphisms of `W` and of `W'` agree across the base change of `u`**: the
hypothesis under which the identification of `H^k` of the thickening ideal is natural.

```
  g^*((i₀)_* (𝒪_{W ×_T T₀} ^ ι)) ──g^* Φ──▶ g^* Iₙ
              │                                 │ comapModulesMap
   baseChange │                                 ▼
              ▼                                 │
  (i'₀)_* (g₀^* (𝒪_{W ×_T T₀} ^ ι)) ──(i'₀)_* pullbackFreeIso──▶ (i'₀)_* (𝒪_{W' ×_T T₀} ^ ι)
                                                                  ──Φ'──▶ I'ₙ
```

It is the only piece of data that the identification depends on and that the morphism `u` does
not determine: the two families `m` and `m'` of global sections are chosen independently on `W`
and on `W'`. -/
abbrev PushforwardFreeToThickeningIdealBaseChange : Prop :=
  (Modules.pullback (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))).map
        (pushforwardFreeToThickeningIdeal f t n m) ≫
      IdealSheafData.comapModulesMap (thickeningIdeal f t n) (thickeningIdeal f' t n)
        (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
        (comap_thickeningIdeal_le f f' u hu t n) =
    (Modules.baseChange
          (infinitesimalBaseChangeMapOver_comp_mapZero f f' u hu t n)).natTrans.app
        ((infinitesimalBaseChange f t 0).freeModules ι) ≫
      (Modules.pushforward (infinitesimalBaseChangeMapZero f' t n)).map
          (Modules.pullbackFreeIso (infinitesimalBaseChangeMapOver f f' u hu t 0) ι).hom ≫
        pushforwardFreeToThickeningIdeal f' t n m'

variable (hΦ : PushforwardFreeToThickeningIdealBaseChange f f' u hu t n m m')

include hΦ

/-- **The identification of `H^k` of a free thickening ideal is natural in the scheme**, in the
form that assembles a family of classes on the zeroth neighbourhood: pulling the assembled class
back along the base change of `u : W' ⟶ W` is assembling the pullbacks of the members of the
family. -/
theorem thickeningH1FreeAddEquiv_symm_naturality
    (p : ι → (infinitesimalBaseChange f t 0).structureModules.H k) :
    Modules.H.map
        (IdealSheafData.comapModulesMap (thickeningIdeal f t n) (thickeningIdeal f' t n)
          (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
          (comap_thickeningIdeal_le f f' u hu t n)) k
        (Modules.H.pullbackAddHom (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
          (thickeningIdeal f t n).toModules k
          ((thickeningH1FreeAddEquiv f t n m k).symm p)) =
      (thickeningH1FreeAddEquiv f' t n m' k).symm fun j ↦
        Modules.H.structurePullbackMap (infinitesimalBaseChangeMapOver f f' u hu t 0) k (p j) := by
  rw [thickeningH1FreeAddEquiv_symm_apply, thickeningH1FreeAddEquiv_symm_apply]
  exact Modules.H.map_pullbackAddHom_pushforwardAddEquiv_freeLinearEquiv_symm
    (infinitesimalBaseChangeMapOver_comp_mapZero f f' u hu t n) _ _ _ hΦ k p

/-- **The identification of `H^k` of a free thickening ideal is natural in the scheme**: the
`j`-th component of the identification of a class pulled back along the base change of
`u : W' ⟶ W` is the pullback of the `j`-th component of the identification of the class.

```
  H^k(W ×_T T_{n+1}, Iₙ) ──thickeningH1FreeAddEquiv──▶ (ι → H^k(W ×_T T₀, 𝒪))
            │                                                   │
            │ pullback along the base change of `u`             │ structurePullbackMap
            ▼                                                   ▼
  H^k(W' ×_T T_{n+1}, I'ₙ) ─thickeningH1FreeAddEquiv─▶ (ι → H^k(W' ×_T T₀, 𝒪))
```
-/
theorem thickeningH1FreeAddEquiv_naturality
    (x : (thickeningIdeal f t n).toModules.H k) (j : ι) :
    thickeningH1FreeAddEquiv f' t n m' k
        (Modules.H.map
          (IdealSheafData.comapModulesMap (thickeningIdeal f t n) (thickeningIdeal f' t n)
            (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
            (comap_thickeningIdeal_le f f' u hu t n)) k
          (Modules.H.pullbackAddHom (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
            (thickeningIdeal f t n).toModules k x)) j =
      Modules.H.structurePullbackMap (infinitesimalBaseChangeMapOver f f' u hu t 0) k
        (thickeningH1FreeAddEquiv f t n m k x j) := by
  have h := thickeningH1FreeAddEquiv_symm_naturality f f' u hu t n m m' k hΦ
    (thickeningH1FreeAddEquiv f t n m k x)
  rw [AddEquiv.symm_apply_apply] at h
  rw [h, AddEquiv.apply_symm_apply]

/-- **The identification of `H¹` of a free thickening ideal intertwines
`AlgebraicGeometry.Scheme.thickeningH1Map` with the `ι`-fold power of the pullback map on `H¹`
of the structure sheaf of the zeroth infinitesimal neighbourhood.**

This is `AlgebraicGeometry.Scheme.thickeningH1FreeAddEquiv_naturality` in the multiplicative
form in which the group of deformation classes enters the naturality ladder of
`WeilConjectures.AlgebraicGeometry.Cohomology.Thickening`. -/
theorem toAdd_thickeningH1FreeMulEquiv_thickeningH1Map
    (x : Multiplicative ((thickeningIdeal f t n).toModules.H 1)) (j : ι) :
    Multiplicative.toAdd
        (thickeningH1FreeMulEquiv f' t n m' 1 (thickeningH1Map f f' u hu t n x)) j =
      Modules.H.structurePullbackMap (infinitesimalBaseChangeMapOver f f' u hu t 0) 1
        (Multiplicative.toAdd (thickeningH1FreeMulEquiv f t n m 1 x) j) :=
  thickeningH1FreeAddEquiv_naturality f f' u hu t n m m' 1 hΦ (Multiplicative.toAdd x) j

end AlgebraicGeometry.Scheme
