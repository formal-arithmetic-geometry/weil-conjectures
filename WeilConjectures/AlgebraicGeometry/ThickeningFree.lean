/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk

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

The point of the comparison morphism is that it is an isomorphism when the `m j` are the
images of a `κ(t)`-basis of `𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`: the ideal `Iₙ` is the pullback to
`W ×_T T₀` of that vector space. This is **not** proved here, and is the subject of a later
file.

The families `m` it is applied to are produced here. Writing `B = 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2)` and
`K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` for the kernel of the transition map of the
infinitesimal rings, an element of `K` acts on `W ×_T T_{n+1}` by a function vanishing on
`W ×_T Tₙ`, that is by a section of `Iₙ` over `⊤`; lifting that section along the inclusion
`Iₙ ↪ 𝒪_{W ×_T T_{n+1}}` of sheaves of modules turns a family in `K` into a family
`m : ι → Γ(Iₙ, ⊤)`.

## Main definitions

- `AlgebraicGeometry.Scheme.pushforwardStructureToThickeningIdeal` — multiplication by a global
  section of the thickening ideal, as a morphism `(i₀)_* 𝒪_{W ×_T T₀} ⟶ Iₙ`.
- `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` — the comparison morphism
  `(i₀)_* (𝒪_{W ×_T T₀} ^ ι) ⟶ Iₙ` attached to a family of global sections of `Iₙ`.

## Main results

- `AlgebraicGeometry.Scheme.infinitesimalRingToΓ_mem_idealOfOpens_thickeningIdeal_of_mem_ker` —
  an element of `K` acts on `W ×_T T_{n+1}` by a section of `Iₙ` over `⊤`.
- `AlgebraicGeometry.Scheme.exists_forall_toModulesι_app_eq_infinitesimalRingToΓ_of_mem_ker` — a
  family of elements of `K` is realized by a family of global sections of `Iₙ` as a sheaf of
  modules.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

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

It is an isomorphism when the `m j` are the images of a `κ(t)`-basis of
`𝔪_t ^ (n + 1) ⧸ 𝔪_t ^ (n + 2)`; that is not proved here. -/
noncomputable abbrev pushforwardFreeToThickeningIdeal {ι : Type u} [Finite ι]
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (Modules.pushforward (infinitesimalBaseChangeMapZero f t n)).obj
        ((infinitesimalBaseChange f t 0).freeModules ι) ⟶ (thickeningIdeal f t n).toModules :=
  IdealSheafData.pushforwardFreeDesc _ (ker_mul_thickeningIdeal_eq_zero f t n) m

/-- **An element of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` acts on `W ×_T T_{n+1}` by a global
section of the thickening ideal `Iₙ`**: its image under
`AlgebraicGeometry.Scheme.infinitesimalRingToΓ` lies in `Iₙ` over `⊤`.

```
                   infinitesimalRingToΓ f t (n + 1)
  B = 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 2) ──────────────────────▶ Γ(W ×_T T_{n+1}, 𝒪)
             │                                                   │
             │ infinitesimalRingMap t (Nat.le_succ n)             │ appTop of
             │                                                   │ infinitesimalBaseChangeMap
             ▼                                                   ▼
  𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1) ────────────────────────────▶ Γ(W ×_T Tₙ, 𝒪)
                     infinitesimalRingToΓ f t n
```

An element `b` of `K` is killed by the left-hand map, hence by the left-then-bottom composite,
hence by the top-then-right one: its image in `Γ(W ×_T T_{n+1}, 𝒪)` restricts to `0` on
`W ×_T Tₙ`, which is membership in the kernel ideal sheaf `Iₙ`. -/
theorem infinitesimalRingToΓ_mem_idealOfOpens_thickeningIdeal_of_mem_ker
    {b : T.infinitesimalRing t (n + 1)}
    (hb : b ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    infinitesimalRingToΓ f t (n + 1) b ∈ (thickeningIdeal f t n).idealOfOpens ⊤ := by
  rw [thickeningIdeal, Scheme.Hom.mem_idealOfOpens_ker_iff]
  have hb' := ConcreteCategory.congr_hom (infinitesimalRingToΓ_comp_appTop f t (Nat.le_succ n)) b
  simp only [CommRingCat.comp_apply] at hb'
  exact hb'.trans (by rw [RingHom.mem_ker.mp hb, map_zero])

/-- **An element of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is realized by a global section of
the thickening ideal as a sheaf of modules**, lying over its image in `Γ(W ×_T T_{n+1}, 𝒪)`.

```
                                  Γ(Iₙ, ⊤)
                                ╱     │
                        ∃ m   ╱       │ toModulesι.app ⊤
                            ╱         ▼
  b ∈ K ──infinitesimalRingToΓ f t (n + 1)──▶ Γ(W ×_T T_{n+1}, 𝒪)
```

The lift exists because the sections of `Iₙ` as a sheaf of modules over `⊤` are exactly the
sections of `𝒪_{W ×_T T_{n+1}}` lying in the ideal `Iₙ` over `⊤`. -/
theorem exists_toModulesι_app_eq_infinitesimalRingToΓ_of_mem_ker
    {b : T.infinitesimalRing t (n + 1)}
    (hb : b ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    ∃ m : Γ((thickeningIdeal f t n).toModules, ⊤),
      (thickeningIdeal f t n).toModulesι.app ⊤ m = infinitesimalRingToΓ f t (n + 1) b :=
  (IdealSheafData.range_toModulesι_app_eq_idealOfOpens _ ⊤).ge
    (infinitesimalRingToΓ_mem_idealOfOpens_thickeningIdeal_of_mem_ker f t n hb)

/-- **A family of elements of `K = ker (B ⟶ 𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1))` is realized by a family
of global sections of the thickening ideal as a sheaf of modules.** This is the family to feed
to `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal`. -/
theorem exists_forall_toModulesι_app_eq_infinitesimalRingToΓ_of_mem_ker {ι : Type*}
    (e : ι → T.infinitesimalRing t (n + 1))
    (he : ∀ j, e j ∈ RingHom.ker (T.infinitesimalRingMap t (Nat.le_succ n)).hom) :
    ∃ m : ι → Γ((thickeningIdeal f t n).toModules, ⊤),
      ∀ j, (thickeningIdeal f t n).toModulesι.app ⊤ (m j) =
        infinitesimalRingToΓ f t (n + 1) (e j) := by
  choose m hm using fun j ↦
    exists_toModulesι_app_eq_infinitesimalRingToΓ_of_mem_ker f t n (he j)
  exact ⟨m, hm⟩

end AlgebraicGeometry.Scheme
