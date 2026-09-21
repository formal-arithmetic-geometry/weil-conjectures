/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk
public import WeilConjectures.Mathlib.RingTheory.Ideal.Cotangent

/-!
# The comparison morphism from a free module on the zeroth infinitesimal neighbourhood

Let `f : W ⟶ T` be a morphism of schemes, let `t` be a point of `T`, let `Tₙ` be the `n`-th
infinitesimal neighbourhood of `t` and let `Iₙ` be the thickening ideal of
`W ×_T Tₙ ↪ W ×_T T_{n+1}`. Write `i₀ : W ×_T T₀ ↪ W ×_T T_{n+1}` for the closed immersion of
the zeroth infinitesimal neighbourhood.

The ideal `Iₙ` is killed by the ideal sheaf of `i₀`
(`AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`), so multiplication by a global
section `m` of `Iₙ` descends from `𝒪_{W ×_T T_{n+1}}` to the quotient `(i₀)_* 𝒪_{W ×_T T₀}`.
Taking a finite family `m : ι → Γ(Iₙ, ⊤)` and using that the pushforward preserves finite
coproducts assembles these into the comparison morphism

```
  (i₀)_* (𝒪_{W ×_T T₀} ^ ι) ⟶ Iₙ
```

of `𝒪_{W ×_T T_{n+1}}`-modules. Both are instances of the general construction of
`AlgebraicGeometry.Scheme.IdealSheafData.pushforwardFreeDesc`, which needs nothing about
thickenings beyond the vanishing `g.ker * Iₙ = 0`.

The point of the comparison morphism is that it is an isomorphism when `f` is flat and the
`m j` are the images of a `κ(t)`-basis of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`: the ideal `Iₙ` is
the pullback to `W ×_T T₀` of that vector space. This is **not** proved here; it is
`AlgebraicGeometry.Scheme.isIso_pushforwardFreeToThickeningIdeal`, in
`WeilConjectures.AlgebraicGeometry.ThickeningFlat`.

The family of global sections to feed to the comparison morphism is produced here, though.
Writing `B = 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2)` and `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))`, the ideal
`K` is annihilated by the maximal ideal of `B`, so it is a `κ(t)`-vector space; a `κ(t)`-basis
of it lifts to a family `e : ι → B` spanning `K` and with all relations having coefficients in
`𝔪_B` (`IsLocalRing.exists_span_eq_of_maximalIdeal_mul_eq_bot`). Each `e j` acts on
`W ×_T T_{n+1}` by a global section of `Iₙ`, and lifting that section along the inclusion
`Iₙ ↪ 𝒪_{W ×_T T_{n+1}}` of sheaves of modules gives the family `m : ι → Γ(Iₙ, ⊤)`.

## Main definitions

- `AlgebraicGeometry.Scheme.pushforwardStructureToThickeningIdeal` — multiplication by a global
  section of the thickening ideal, as a morphism `(i₀)_* 𝒪_{W ×_T T₀} ⟶ Iₙ`.
- `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` — the comparison morphism
  `(i₀)_* (𝒪_{W ×_T T₀} ^ ι) ⟶ Iₙ` attached to a family of global sections of `Iₙ`.

## Main results

- `AlgebraicGeometry.Scheme.exists_forall_toModulesι_app_eq_infinitesimalRingToΓ` — a family of
  elements of `K` is realized by a family of global sections of `Iₙ`.
- `AlgebraicGeometry.Scheme.exists_span_eq_and_forall_toModulesι_app_eq` — the two together: a
  finite family `e` spanning `K` with all relations having coefficients in `𝔪_B`, and a family
  `m` of global sections of `Iₙ` lying over it.
- `AlgebraicGeometry.Scheme.isPushforwardFreeToThickeningIdealBaseChange_of_toModulesι_app_eq`
  — **the comparison morphisms of `W` and of `W'` agree across the base change of a morphism
  `u : W' ⟶ W` over `T`**, as soon as the two families of global sections lie over one family
  `e` of elements of `B`. Since `e` is a datum on the base `(T, t)`, which `f` and `f'` share,
  this is what the previous item produces. The statement of the compatibility is
  `AlgebraicGeometry.Scheme.IsPushforwardFreeToThickeningIdealBaseChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Comparison

variable {T W : Scheme.{u}} (f : W ⟶ T) (t : T) (n : ℕ)

/-- **Multiplication by a global section `m` of the thickening ideal**, as a morphism
`(i₀)_* 𝒪_{W ×_T T₀} ⟶ Iₙ`, where `i₀ : W ×_T T₀ ↪ W ×_T T_{n+1}` is the closed immersion of
the zeroth infinitesimal neighbourhood.

```
  𝒪_{W ×_T T_{n+1}} ──toPushforwardStructure──▶ (i₀)_* 𝒪_{W ×_T T₀}
                  ╲                                     │
             · m   ╲                                    │ multiplication by `m`
                    ╲                                   ▼
                     ╲────────────────────────────────▶ Iₙ
```

This is `AlgebraicGeometry.Scheme.IdealSheafData.pushforwardStructureDesc` for the vanishing
`AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`, so the lemmas
`IdealSheafData.toPushforwardStructure_comp_pushforwardStructureDesc` and
`IdealSheafData.eq_pushforwardStructureDesc` apply to it and say that the triangle above
determines it. -/
noncomputable abbrev pushforwardStructureToThickeningIdeal
    (m : Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (Modules.pushforward (infinitesimalBaseChangeMapZero f t n)).obj
        (infinitesimalBaseChange f t 0).structureModules ⟶ (thickeningIdeal f t n).toModules :=
  IdealSheafData.pushforwardStructureDesc _ (ker_mul_thickeningIdeal_eq_zero f t n) m

/-- **The comparison morphism `(i₀)_* (𝒪_{W ×_T T₀} ^ ι) ⟶ Iₙ` attached to a family `m` of
global sections of the thickening ideal**: on the `j`-th summand it is multiplication by `m j`.

```
  (i₀)_* 𝒪_{W ×_T T₀} ──(i₀)_* (ιFree j)──▶ (i₀)_* (𝒪_{W ×_T T₀} ^ ι)
                    ╲                                   │
             · m j   ╲                                  │ comparison morphism
                      ╲                                 ▼
                       ╲──────────────────────────────▶ Iₙ
```

This is `AlgebraicGeometry.Scheme.IdealSheafData.pushforwardFreeDesc` for the vanishing
`AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`, so the lemmas
`IdealSheafData.map_ιFree_comp_pushforwardFreeDesc` and
`IdealSheafData.eq_pushforwardFreeDesc` apply to it and say that the triangles above
determine it.

It is an isomorphism when `f` is flat and the `m j` are the images of a `κ(t)`-basis of
`𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`; that is
`AlgebraicGeometry.Scheme.isIso_pushforwardFreeToThickeningIdeal`, proved in
`WeilConjectures.AlgebraicGeometry.ThickeningFlat`. -/
noncomputable abbrev pushforwardFreeToThickeningIdeal {ι : Type u} [Finite ι]
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (Modules.pushforward (infinitesimalBaseChangeMapZero f t n)).obj
        ((infinitesimalBaseChange f t 0).freeModules ι) ⟶ (thickeningIdeal f t n).toModules :=
  IdealSheafData.pushforwardFreeDesc _ (ker_mul_thickeningIdeal_eq_zero f t n) m

section Sections

/-- An element of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` acts on `W ×_T T_{n+1}` by a global
section of the thickening ideal `Iₙ`: its image under
`AlgebraicGeometry.Scheme.infinitesimalRingToΓ` lies in `Iₙ` over `⊤`. -/
theorem infinitesimalRingToΓ_mem_idealOfOpens_thickeningIdeal
    {b : T.infinitesimalRing t (n + 1)}
    (hb : b ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    infinitesimalRingToΓ f t (n + 1) b ∈ (thickeningIdeal f t n).idealOfOpens ⊤ := by
  rw [thickeningIdeal, Scheme.Hom.mem_idealOfOpens_ker_iff]
  have hb' := ConcreteCategory.congr_hom (infinitesimalRingToΓ_comp_appTop f t (Nat.le_succ n)) b
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hb'
  have hb'' : (infinitesimalBaseChangeMap f t (Nat.le_succ n)).appTop
      (infinitesimalRingToΓ f t (n + 1) b) = 0 := by
    rw [hb', RingHom.mem_ker.mp hb, map_zero]
  exact hb''

/-- **An element of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is realized by a global section of
the thickening ideal as a sheaf of modules**, lying over its image in `Γ(W ×_T T_{n+1}, 𝒪)`. -/
theorem exists_toModulesι_app_eq_infinitesimalRingToΓ
    {b : T.infinitesimalRing t (n + 1)}
    (hb : b ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    ∃ m : Γ((thickeningIdeal f t n).toModules, ⊤),
      (thickeningIdeal f t n).toModulesι.app ⊤ m = infinitesimalRingToΓ f t (n + 1) b :=
  (IdealSheafData.range_toModulesι_app_eq_idealOfOpens _ ⊤).ge
    (infinitesimalRingToΓ_mem_idealOfOpens_thickeningIdeal f t n hb)

/-- **A family of elements of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is realized by a family
of global sections of the thickening ideal as a sheaf of modules.** -/
theorem exists_forall_toModulesι_app_eq_infinitesimalRingToΓ {ι : Type*}
    (e : ι → T.infinitesimalRing t (n + 1))
    (he : ∀ j, e j ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    ∃ m : ι → Γ((thickeningIdeal f t n).toModules, ⊤),
      ∀ j, (thickeningIdeal f t n).toModulesι.app ⊤ (m j) =
        infinitesimalRingToΓ f t (n + 1) (e j) := by
  choose m hm using fun j ↦ exists_toModulesι_app_eq_infinitesimalRingToΓ f t n (he j)
  exact ⟨m, hm⟩

/-- **A residue-field basis of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))`, both as a spanning
family with all relations having coefficients in `𝔪_B` and as a family of global sections of the
thickening ideal.** The index type lives in the universe of the schemes, so that the family `m`
can be fed to `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal`.

The spanning and independence statements are exactly the hypotheses of
`Ideal.range_linearCombination_algebraMap` and `Ideal.ker_linearCombination_eq_pi`, and the last
one is what identifies the sections `m j` with the elements `e j` of `B`. -/
theorem exists_span_eq_and_forall_toModulesι_app_eq
    (hfg : (RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom).FG) :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → T.infinitesimalRing t (n + 1))
      (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)),
      Ideal.span (Set.range e) =
          RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom ∧
      (∀ c : ι → T.infinitesimalRing t (n + 1), ∑ i, c i * e i = 0 →
        ∀ i, c i ∈ IsLocalRing.maximalIdeal (T.infinitesimalRing t (n + 1))) ∧
      (∀ j, (thickeningIdeal f t n).toModulesι.app ⊤ (m j) =
        infinitesimalRingToΓ f t (n + 1) (e j)) := by
  obtain ⟨ι, hι, e, hspan, hind, -⟩ :=
    IsLocalRing.exists_span_eq_of_maximalIdeal_mul_eq_bot
      (T.maximalIdeal_mul_ker_infinitesimalRingMap t n) hfg
  obtain ⟨m, hm⟩ := exists_forall_toModulesι_app_eq_infinitesimalRingToΓ f t n e
    fun j ↦ hspan ▸ Ideal.subset_span ⟨j, rfl⟩
  exact ⟨ι, hι, e, m, hspan, hind, hm⟩

end Sections

end Comparison

/-! ### Base change in the scheme -/

section BaseChange

variable {T W W' : Scheme.{u}} (f : W ⟶ T) (f' : W' ⟶ T) (u : W' ⟶ W) (hu : u ≫ f = f')
  (t : T) (n : ℕ) {ι : Type u} [Finite ι]
  (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
  (m' : ι → Γ((thickeningIdeal f' t n).toModules, ⊤))

/-- **The comparison morphisms of `W` and of `W'` agree across the base change of a morphism
`u : W' ⟶ W` over `T`.**

Write `g` and `g₀` for the base changes of `u` to the `(n + 1)`-st and to the zeroth
infinitesimal neighbourhood, and `Φ` and `Φ'` for the comparison morphisms
`AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` attached to `m` on `W` and to `m'`
on `W'`. The square is

```
  g^*((i₀)_*(𝒪_{W₀}^ι)) ──g^* Φ──▶ g^* Iₙ ──comapModulesMap──▶ I'ₙ
            │                                                   ▲
            │ baseChange                                        │ Φ'
            ▼                                                   │
  (i'₀)_*(g₀^*(𝒪_{W₀}^ι)) ──(i'₀)_* pullbackFreeIso──▶ (i'₀)_*(𝒪_{W'₀}^ι)
```

It holds as soon as the two families `m` and `m'` lie over one family of elements of
`𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2)`, by
`AlgebraicGeometry.Scheme.isPushforwardFreeToThickeningIdealBaseChange_of_toModulesι_app_eq`. -/
abbrev IsPushforwardFreeToThickeningIdealBaseChange : Prop :=
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

/-- **The comparison morphisms agree across the base change of `u` as soon as the two families
of global sections do**, section by section: this is
`AlgebraicGeometry.Scheme.IdealSheafData.pullback_map_pushforwardFreeDesc_comp_comapModulesMap`
for the thickening ideal. -/
theorem isPushforwardFreeToThickeningIdealBaseChange_of_appTop_toModulesι_app_eq
    (hmm' : ∀ j, (infinitesimalBaseChangeMapOver f f' u hu t (n + 1)).appTop
        (Modules.Hom.app (thickeningIdeal f t n).toModulesι ⊤ (m j)) =
      Modules.Hom.app (thickeningIdeal f' t n).toModulesι ⊤ (m' j)) :
    IsPushforwardFreeToThickeningIdealBaseChange f f' u hu t n m m' :=
  IdealSheafData.pullback_map_pushforwardFreeDesc_comp_comapModulesMap
    (ker_mul_thickeningIdeal_eq_zero f t n) (ker_mul_thickeningIdeal_eq_zero f' t n)
    (comap_thickeningIdeal_le f f' u hu t n)
    (infinitesimalBaseChangeMapOver_comp_mapZero f f' u hu t n) m m' hmm'

/-- **The comparison morphisms agree across the base change of `u` when the two families of
global sections lie over one family `e` of elements of `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2)`.**

That is the situation the comparison morphism is built for:
`AlgebraicGeometry.Scheme.exists_span_eq_and_forall_toModulesι_app_eq` produces `e` on the base
`(T, t)`, which `f` and `f'` share, and a family `m` lying over it for each of them. -/
theorem isPushforwardFreeToThickeningIdealBaseChange_of_toModulesι_app_eq
    {e : ι → T.infinitesimalRing t (n + 1)}
    (hm : ∀ j, Modules.Hom.app (thickeningIdeal f t n).toModulesι ⊤ (m j) =
      infinitesimalRingToΓ f t (n + 1) (e j))
    (hm' : ∀ j, Modules.Hom.app (thickeningIdeal f' t n).toModulesι ⊤ (m' j) =
      infinitesimalRingToΓ f' t (n + 1) (e j)) :
    IsPushforwardFreeToThickeningIdealBaseChange f f' u hu t n m m' :=
  isPushforwardFreeToThickeningIdealBaseChange_of_appTop_toModulesι_app_eq f f' u hu t n m m'
    fun j ↦ by
      rw [hm, hm', ← CommRingCat.comp_apply, infinitesimalRingToΓ_comp_mapOver_appTop]

end BaseChange

end AlgebraicGeometry.Scheme
