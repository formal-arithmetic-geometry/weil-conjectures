/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Group.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PicardField
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# A line bundle pulled back along a constant morphism is trivial

Let `K` be a field, let `S` and `V` be `K`-schemes and let `v ∈ V(K)` be a `K`-rational point of
`V`. The *constant morphism at `v`* is the composite `π ≫ v : S ⟶ V` of the structure morphism
`π : S ⟶ Spec K` with `v : Spec K ⟶ V`:

```
              π                v
       S ──────────→ Spec K ──────────→ V
        ╲                              ↗
         ╲─────────── π ≫ v ──────────╱
```

This file proves that every line bundle on `V` pulls back along such a composite to the
structure sheaf of `S`.

Nothing about fields is used. The only thing the argument needs is that the Picard group of the
intermediate scheme is trivial, so the statements below are made for an arbitrary intermediate
scheme `T` with `[Subsingleton T.Pic]`. The `K`-scheme form is recovered by instance search at
`T := Spec K`, through `AlgebraicGeometry.Scheme.Pic.subsingleton_spec_field`.

The proof is the blueprint's, read in the Picard group: pullback is pseudofunctorial, so
`Pic.map (π ≫ v) = Pic.map π ∘ Pic.map v`, and `Pic.map v` takes its values in the trivial
group `T.Pic`. Unwinding the Picard classes turns this into the chain of isomorphisms

```
   (π ≫ v)^* N  ≅  π^* (v^* N)  ≅  π^* 𝒪_T  ≅  𝒪_S
```

whose middle step is the triviality of the line bundle `v^* N` on `T` and whose last step is the
monoidality of `π^*`.

## Main results

- `AlgebraicGeometry.Scheme.Pic.map_comp_eq_one`: pullback along `π ≫ v` is the trivial
  homomorphism `V.Pic →* S.Pic`, as soon as `T.Pic` is trivial.
- `SheafOfModules.Invertible.nonempty_pullback_comp_iso_tensorUnit`: the same statement read on
  line bundles, the pullback of a line bundle `N` on `V` along `π ≫ v` being isomorphic to the
  structure sheaf of `S`.
- `SheafOfModules.Invertible.nonempty_pullback_toUnit_comp_iso_tensorUnit`: the same, for `S`
  and `V` presented as objects of `Over B` and a section `v : 𝟙_ (Over B) ⟶ V`, the constant
  morphism at `v` being `toUnit S ≫ v`.
- `AlgebraicGeometry.Scheme.Pic.map_one_left`: the special case of a monoid scheme `G` over `B`
  and its unit section, so that the constant morphism is the trivial `W`-point `1 : W ⟶ G`.

## Implementation notes

The trivialisations are isomorphisms with the tensor unit `𝟙_ S.Modules`.
`AlgebraicGeometry.Scheme.Modules.tensorUnitIsoUnit` turns such an isomorphism into one with the
structure sheaf `SheafOfModules.unit S.ringCatSheaf`, which is the form the statements of
`WeilConjectures.AlgebraicGeometry.Modules.TrivialLineBundle` consume.

## Blueprint

This file proves `lem:cube-pullback-constant` of the theorem-of-the-cube chapter,
`blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`, in the
tensor-invertible spelling of a line bundle: `SheafOfModules.Invertible`, rather than local
freeness of rank one. That is the spelling in which the input from `sec:cube-cost` (N3) — the
triviality of the Picard group of the spectrum of a field — is available, and the spelling in
which the consumers of the chapter state ampleness, so no bridge between the two is needed.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.Scheme

variable {S T V : Scheme.{u}} [Subsingleton T.Pic]

/-- **The pullback along a morphism which factors through a scheme with trivial Picard group
kills every Picard class.** If `π : S ⟶ T` and `v : T ⟶ V` and the Picard group of `T` is
trivial — for instance `T = Spec K` for a field `K` — then the class of a line bundle `N` on `V`
pulls back to the trivial class on `S`. -/
theorem Pic.map_comp_apply_eq_one (π : S ⟶ T) (v : T ⟶ V) (x : V.Pic) :
    Pic.map (π ≫ v) x = 1 := by
  rw [Pic.map_comp_apply, Subsingleton.elim (Pic.map v x) 1, map_one]

/-- **Pullback along a morphism which factors through a scheme with trivial Picard group is the
trivial homomorphism of Picard groups.** -/
theorem Pic.map_comp_eq_one (π : S ⟶ T) (v : T ⟶ V) : Pic.map (π ≫ v) = 1 :=
  MonoidHom.ext fun x ↦ (Pic.map_comp_apply_eq_one π v x).trans (MonoidHom.one_apply x).symm

/-- **A line bundle pulled back along a constant morphism is trivial.** Let `π : S ⟶ T` and
`v : T ⟶ V` be morphisms of schemes and assume the Picard group of `T` is trivial — for instance
`T = Spec K` for a field `K`, `π` the structure morphism of a `K`-scheme `S` and `v` a
`K`-rational point of `V`, so that `π ≫ v` is the constant morphism at `v`:

```
              π              v
       S ──────────→ T ──────────→ V
        ╲                         ↗
         ╲────────── π ≫ v ──────╱
```

Then the pullback of a line bundle `N` on `V` along `π ≫ v` is isomorphic to the structure sheaf
of `S`. -/
theorem _root_.SheafOfModules.Invertible.nonempty_pullback_comp_iso_tensorUnit {N : V.Modules}
    (hN : N.Invertible) (π : S ⟶ T) (v : T ⟶ V) :
    Nonempty ((Modules.pullback (π ≫ v)).obj N ≅ 𝟙_ S.Modules) :=
  (Pic.mk_eq_one_iff (hM := hN.pullback (π ≫ v))).1 <| by
    rw [← Pic.map_mk (π ≫ v) hN, Pic.map_comp_apply_eq_one]

section OverBase

variable {B : Scheme.{u}} [Subsingleton B.Pic] {S V : Over B}

/-- **A line bundle pulled back along a constant morphism is trivial**, for `S` and `V` presented
as objects of `Over B` over a base scheme `B` with trivial Picard group — for instance
`B = Spec K` for a field `K` — and a section `v : 𝟙_ (Over B) ⟶ V`, the constant morphism at `v`
being `toUnit S ≫ v`. -/
theorem _root_.SheafOfModules.Invertible.nonempty_pullback_toUnit_comp_iso_tensorUnit
    {N : V.left.Modules} (hN : N.Invertible) (v : 𝟙_ (Over B) ⟶ V) :
    Nonempty ((Modules.pullback (toUnit S ≫ v).left).obj N ≅ 𝟙_ S.left.Modules) :=
  hN.nonempty_pullback_comp_iso_tensorUnit S.hom v.left

/-- **A Picard class pulled back along the constant morphism at the unit of a monoid scheme is
trivial.** For a monoid scheme `G` over a base `B` with trivial Picard group, the trivial
`W`-point `1 : W ⟶ G` is, on underlying schemes, the constant morphism at the unit section
`η[G].left` (`AlgebraicGeometry.MonObj.one_left`), so this is the case `v = η[G]` of
`AlgebraicGeometry.Scheme.Pic.map_comp_apply_eq_one`. -/
@[simp]
theorem Pic.map_one_left {G W : Over B} [MonObj G] (ℓ : G.left.Pic) :
    Pic.map (1 : W ⟶ G).left ℓ = 1 := by
  rw [MonObj.one_left]
  exact Pic.map_comp_apply_eq_one W.hom η[G].left ℓ

end OverBase

end AlgebraicGeometry.Scheme
