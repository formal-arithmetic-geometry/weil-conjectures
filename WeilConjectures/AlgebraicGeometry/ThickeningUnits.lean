/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Thickening
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Units of the infinitesimal thickenings of a proper variety

Let `X` be a proper geometrically integral variety over a field `K`, let `Z` be a `K`-scheme and
let `t` be a point of `Z`. Writing `Aₙ := 𝒪_{Z, t} ⧸ 𝔪_t ^ (n + 1)` and `Zₙ := Spec Aₙ`, this
file computes the global sections of the tower

```
  (X ×_K Z) ×_Z Z₀ ↪ (X ×_K Z) ×_Z Z₁ ↪ ⋯ ↪ (X ×_K Z) ×_Z Zₙ ↪ ⋯
```

of infinitesimal base changes of `X ×_K Z ⟶ Z`: they are the rings `Aₙ`, because pasting the
two cartesian squares identifies `(X ×_K Z) ×_Z Zₙ` with `X ×_K Spec Aₙ`. Since `Aₙ₊₁` is a
local ring surjecting onto `Aₙ`, units lift along each step of the tower.

## Main statements

- `AlgebraicGeometry.Scheme.isIso_infinitesimalRingToΓ_pullbackSnd` — the global sections of
  `(X ×_K Z) ×_Z Zₙ` are `Aₙ`.
- `AlgebraicGeometry.Scheme.unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective` — every
  unit on `(X ×_K Z) ×_Z Zₙ` is the restriction of a unit on `(X ×_K Z) ×_Z Z_{n+1}`. This is
  the unit-extension hypothesis of the theorem of the cube, in
  `WeilConjectures.AlgebraicGeometry.TheoremOfCube`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- **The global sections of `(X ×_K Z) ×_Z Zₙ` are the infinitesimal ring `Aₙ`.**

For `X` a proper geometrically integral variety over a field `K`, `Z` a `K`-scheme and `t` a
point of `Z`, the `n`-th infinitesimal base change of `X ×_K Z ⟶ Z` is `X ×_K Spec Aₙ` with
`Aₙ = 𝒪_{Z, t} ⧸ 𝔪_t ^ (n + 1)`, so its global sections are `Aₙ`. This is the specialisation to
`Zₙ ⟶ Z` of `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_snd_appTop_pullbackSnd`, which in turn
rests on `lem:cube-global-sections-base-change` of the blueprint. -/
theorem isIso_infinitesimalRingToΓ_pullbackSnd (πX : X ⟶ Spec (.of K)) [IsProper πX]
    [GeometricallyIntegral πX] (πZ : Z ⟶ Spec (.of K)) (t : Z) (n : ℕ) :
    IsIso (infinitesimalRingToΓ (pullback.snd πX πZ) t n) :=
  isIso_ΓSpecIso_inv_comp_snd_appTop_pullbackSnd πX πZ (Z.fromInfinitesimalNeighborhood t n)

/-- **Units of an infinitesimal thickening of a proper variety lift** (blueprint:
`lem:cube-thickening-units`).

For `X` a proper geometrically integral variety over a field `K`, `Z` a `K`-scheme and `t` a
point of `Z`, every unit on the `n`-th infinitesimal thickening `(X ×_K Z) ×_Z Zₙ` extends to
the `(n + 1)`-st, because the global sections of the two are the local rings `Aₙ` and `Aₙ₊₁`
and `Aₙ₊₁ ↠ Aₙ`. This is the unit-extension hypothesis `hX` (and, for `Y` in place of `X`,
`hY`) of the theorem of the cube. -/
theorem unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective (πX : X ⟶ Spec (.of K))
    [IsProper πX] [GeometricallyIntegral πX] (πZ : Z ⟶ Spec (.of K)) (t : Z) (n : ℕ) :
    Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι) :=
  unitsMap_subschemeι_thickeningIdeal_surjective _ t n
    (isIso_infinitesimalRingToΓ_pullbackSnd πX πZ t n)

end AlgebraicGeometry.Scheme
