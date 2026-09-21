/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk

/-!
# Deformation classes along the thickenings of an infinitesimal base change

Let `f : W ⟶ T` be a morphism of schemes, let `t` be a point of `T` and let `Tₙ` be the `n`-th
infinitesimal neighbourhood of `t`. The closed immersion `W ×_T Tₙ ↪ W ×_T T_{n+1}` is a
square-zero thickening (`AlgebraicGeometry.Scheme.sq_thickeningIdeal`), so the five-term
sequence of `WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero` applies to it and
`H¹(W ×_T T_{n+1}, Iₙ)` is the group of deformation classes of line bundles along it.

This file makes that sequence functorial in a morphism `u : W' ⟶ W` over `T`: the base change
`W' ×_T T_{n+1} ⟶ W ×_T T_{n+1}` pulls the thickening ideal of `W` into that of `W'`, giving
the vertical map `AlgebraicGeometry.Scheme.thickeningH1Map` of the ladder

```
  H¹(W ×_T T_{n+1}, Iₙ) ───h1ToPic───▶ Pic (W ×_T T_{n+1})
          │                                    │
          │ thickeningH1Map                    │ Pic.map (base change of u)
          ▼                                    ▼
  H¹(W' ×_T T_{n+1}, I'ₙ) ──h1ToPic──▶ Pic (W' ×_T T_{n+1})
```

and the lemma that reads off the ladder: an obstruction class whose image in
`Pic (W ×_T T_{n+1})` is the class of a line bundle trivial on `W'` has trivial
`W'`-component.

## Main definitions

- `AlgebraicGeometry.Scheme.thickeningH1Map` — the map on deformation classes induced by a
  morphism over `T`.

## Main statements

- `AlgebraicGeometry.Scheme.thickeningH1Map_eq_one_of_pic_map_eq_one` — the naturality ladder
  kills the `W'`-component of an obstruction class of a line bundle that is trivial on `W'`.
- `AlgebraicGeometry.Scheme.unitsMap_subschemeι_thickeningIdeal_surjective` — the hypothesis
  that the previous lemma needs: if the global sections of `W ×_T Tₙ` are the infinitesimal
  ring `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`, then every unit on `W ×_T Tₙ` extends to `W ×_T T_{n+1}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {T W W' : Scheme.{u}} (f : W ⟶ T) (f' : W' ⟶ T) (u : W' ⟶ W) (hu : u ≫ f = f') (t : T)

/-- **The map on deformation classes** `H¹(W ×_T T_{n+1}, Iₙ) ⟶ H¹(W' ×_T T_{n+1}, I'ₙ)`
induced by a morphism `u : W' ⟶ W` over `T`: the middle vertical map of the naturality ladder
of `prop:cube-picard-square-zero`, taken at the base change of `u` and the canonical
comparison morphism of thickening ideals. -/
noncomputable def thickeningH1Map (n : ℕ) :
    Multiplicative ((thickeningIdeal f t n).toModules.H 1) →*
      Multiplicative ((thickeningIdeal f' t n).toModules.H 1) :=
  IdealSheafData.h1MapOfComapLe _ _ (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
    (comap_thickeningIdeal_le f f' u hu t n)

/-- **The map on deformation classes, additively**: `AlgebraicGeometry.Scheme.thickeningH1Map`
is `AlgebraicGeometry.Scheme.IdealSheafData.hMapOfComapLe` in degree one, for the base change
of `u` and the canonical comparison morphism of thickening ideals. -/
@[simp]
lemma toAdd_thickeningH1Map (n : ℕ)
    (x : Multiplicative ((thickeningIdeal f t n).toModules.H 1)) :
    Multiplicative.toAdd (thickeningH1Map f f' u hu t n x) =
      IdealSheafData.hMapOfComapLe (thickeningIdeal f t n) (thickeningIdeal f' t n)
        (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
        (comap_thickeningIdeal_le f f' u hu t n) 1 (Multiplicative.toAdd x) :=
  rfl

/-- **The naturality ladder kills the component of an obstruction class along a morphism over
`T` on which the line bundle is trivial.**

Let `u : W' ⟶ W` be a morphism over `T`, let `M` be a line bundle on `W` whose pullback to
`W'` is trivial, and let `α` be a class in `H¹(W ×_T T_{n+1}, Iₙ)` whose image in
`Pic (W ×_T T_{n+1})` is the class of the pullback of `M`. If every unit on `W' ×_T Tₙ`
extends to `W' ×_T T_{n+1}`, then the `W'`-component of `α` vanishes.

```
        α ∈ H¹(W ×_T T_{n+1}, Iₙ) ───h1ToPic───▶ [M] ∈ Pic (W ×_T T_{n+1})
                  │                                       │
                  │ thickeningH1Map                       │ Pic.map
                  ▼                                       ▼
        H¹(W' ×_T T_{n+1}, I'ₙ) ─────h1ToPic────▶ 1 ∈ Pic (W' ×_T T_{n+1})
```
-/
lemma thickeningH1Map_eq_one_of_pic_map_eq_one (n : ℕ)
    (hu' : Function.Surjective (Hom.unitsMap (thickeningIdeal f' t n).subschemeι))
    {M : W.Modules} (hM : M.Invertible) (hMu : Pic.map u (Pic.mk M hM) = 1)
    (α : Multiplicative ((thickeningIdeal f t n).toModules.H 1))
    (hα : (thickeningIdeal f t n).h1ToPic (sq_thickeningIdeal f t n) α =
      Pic.map (infinitesimalBaseChangeFst f t (n + 1)) (Pic.mk M hM)) :
    thickeningH1Map f f' u hu t n α = 1 := by
  refine IdealSheafData.injective_h1ToPic_of_surjective_unitsMap _
    (sq_thickeningIdeal f' t n) hu' ?_
  rw [map_one, thickeningH1Map, ← MonoidHom.comp_apply,
    ← IdealSheafData.h1ToPic_naturality_comapModulesMap (thickeningIdeal f t n)
      (thickeningIdeal f' t n) (infinitesimalBaseChangeMapOver f f' u hu t (n + 1))
      (sq_thickeningIdeal f t n) (sq_thickeningIdeal f' t n)
      (comap_thickeningIdeal_le f f' u hu t n),
    MonoidHom.comp_apply, hα, ← Pic.map_comp_apply, infinitesimalBaseChangeMapOver_fst,
    Pic.map_comp_apply, hMu, map_one]

/-! ### Units of the thickenings -/

/-- **Units lift along the transition morphisms of the tower**, in terms of
`AlgebraicGeometry.Scheme.Hom.unitsMap`: if the global sections of `W ×_T Tₘ` are the
infinitesimal ring `𝒪_{T, t} ⧸ 𝔪_t ^ (m + 1)`, then for `m ≤ n` every unit on `W ×_T Tₘ` is the
restriction of a unit on `W ×_T Tₙ`. -/
lemma unitsMap_infinitesimalBaseChangeMap_surjective {m n : ℕ} (h : m ≤ n)
    (hm : IsIso (infinitesimalRingToΓ f t m)) :
    Function.Surjective (Hom.unitsMap (infinitesimalBaseChangeMap f t h)) := fun a ↦ by
  obtain ⟨b, hbu, hb⟩ := exists_isUnit_appTop_infinitesimalBaseChangeMap f t h hm a.isUnit
  exact ⟨hbu.unit, Units.ext hb⟩

/-- **Units lift along the thickening `W ×_T Tₙ ↪ W ×_T T_{n+1}`**: if the global sections of
`W ×_T Tₙ` are the infinitesimal ring `𝒪_{T, t} ⧸ 𝔪_t ^ (n + 1)`, then every unit on `W ×_T Tₙ`
extends to `W ×_T T_{n+1}`.

This is the hypothesis `hu'` of
`AlgebraicGeometry.Scheme.thickeningH1Map_eq_one_of_pic_map_eq_one`; the thickening
`V(Iₙ) ↪ W ×_T T_{n+1}` is the transition morphism of the tower up to the isomorphism
`AlgebraicGeometry.Scheme.thickeningIso`. -/
lemma unitsMap_subschemeι_thickeningIdeal_surjective (n : ℕ)
    (hn : IsIso (infinitesimalRingToΓ f t n)) :
    Function.Surjective (Hom.unitsMap (thickeningIdeal f t n).subschemeι) := by
  intro a
  obtain ⟨c, hc⟩ := (Hom.unitsMap_bijective (thickeningIso f t n).inv).2 a
  obtain ⟨b, hb⟩ := unitsMap_infinitesimalBaseChangeMap_surjective f t (Nat.le_succ n) hn c
  refine ⟨b, ?_⟩
  rw [← thickeningIso_inv_infinitesimalBaseChangeMap, Hom.unitsMap_comp, MonoidHom.comp_apply,
    hb, hc]

end AlgebraicGeometry.Scheme
