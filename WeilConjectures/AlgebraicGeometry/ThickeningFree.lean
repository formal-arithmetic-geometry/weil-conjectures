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

## Main definitions

- `AlgebraicGeometry.Scheme.pushforwardStructureToThickeningIdeal` — multiplication by a global
  section of the thickening ideal, as a morphism `(i₀)_* 𝒪_{W ×_T T₀} ⟶ Iₙ`.
- `AlgebraicGeometry.Scheme.pushforwardFreeToThickeningIdeal` — the comparison morphism
  `(i₀)_* (𝒪_{W ×_T T₀} ^ ι) ⟶ Iₙ` attached to a family of global sections of `Iₙ`.
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

end AlgebraicGeometry.Scheme
