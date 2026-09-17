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


/-! ### The comparison morphism from a free module on the zeroth neighbourhood -/

section Free

variable (n : ℕ)

/-- **A function on `W ×_T T_{n+1}` that vanishes on `W ×_T T₀` annihilates the thickening
ideal.** Here `m` is a global section of `Iₙ` and the statement is about its restriction to the
open `U` on which `r` lives.

This is the section-level form of `AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`,
and it is the vanishing that lets multiplication by `m` descend to `W ×_T T₀`; see
`AlgebraicGeometry.Scheme.pushforwardStructureToThickeningIdeal`. -/
lemma smul_thickeningIdealSection_eq_zero (m : Γ((thickeningIdeal f t n).toModules, ⊤))
    {U : (infinitesimalBaseChange f t (n + 1)).Opens}
    (r : Γ(infinitesimalBaseChange f t (n + 1), U))
    (hr : (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))).app U r = 0) :
    r • (thickeningIdeal f t n).toModules.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m = 0 := by
  refine (thickeningIdeal f t n).injective_toModulesι_app U ?_
  have hmem : (thickeningIdeal f t n).toModulesι.app ⊤ m ∈ (thickeningIdeal f t n).idealOfOpens ⊤ :=
    ((thickeningIdeal f t n).range_toModulesι_app_eq_idealOfOpens ⊤).le ⟨m, rfl⟩
  have hres := (thickeningIdeal f t n).map_mem_idealOfOpens (le_top : U ≤ ⊤) hmem
  have hker := (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))).mem_idealOfOpens_ker hr
  calc (thickeningIdeal f t n).toModulesι.app U
          (r • (thickeningIdeal f t n).toModules.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m)
      = r • (thickeningIdeal f t n).toModulesι.app U
          ((thickeningIdeal f t n).toModules.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m) :=
        Modules.Hom.app_smul _ _ _
    _ = r • (infinitesimalBaseChange f t (n + 1)).structureModules.presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op ((thickeningIdeal f t n).toModulesι.app ⊤ m) := by
        rw [Modules.Hom.naturality_apply]
    _ = 0 :=
        IdealSheafData.mul_eq_zero_of_mem_idealOfOpens (ker_mul_thickeningIdeal_eq_zero f t n)
          hker hres
    _ = (thickeningIdeal f t n).toModulesι.app U 0 := (map_zero _).symm

/-- **Multiplication by a global section `m` of the thickening ideal**, as a morphism
`(i₀)_* 𝒪_{W ×_T T₀} ⟶ Iₙ`, where `i₀ : W ×_T T₀ ↪ W ×_T T_{n+1}` is the closed immersion of
the zeroth infinitesimal neighbourhood.

Multiplication by `m` is a morphism `𝒪_{W ×_T T_{n+1}} ⟶ Iₙ` to begin with, and it kills the
ideal sheaf of `W ×_T T₀` by `AlgebraicGeometry.Scheme.ker_mul_thickeningIdeal_eq_zero`, so it
factors through the quotient `(i₀)_* 𝒪_{W ×_T T₀}` of `𝒪_{W ×_T T_{n+1}}`. -/
noncomputable def pushforwardStructureToThickeningIdeal
    (m : Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (Modules.pushforward (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)))).obj
        (infinitesimalBaseChange f t 0).structureModules ⟶ (thickeningIdeal f t n).toModules :=
  (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))).descPushforwardStructure
    ((Modules.unitHomEquivTop _).symm m)
    (((infinitesimalBaseChangeMap f t
        (Nat.zero_le (n + 1))).kernelι_toPushforwardStructure_comp_eq_zero_iff _).mpr
      fun U s hs ↦ by
        have happ := Modules.Hom.app_eq_smul_res
          ((Modules.unitHomEquivTop (thickeningIdeal f t n).toModules).symm m) U s
        rw [Equiv.apply_symm_apply] at happ
        exact happ.trans (smul_thickeningIdealSection_eq_zero f t n m s hs))

/-- **Multiplication by `m` is the factorisation of multiplication by `m` through the
quotient.** -/
@[reassoc (attr := simp)]
lemma toPushforwardStructure_comp_pushforwardStructureToThickeningIdeal
    (m : Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))).toPushforwardStructure ≫
        pushforwardStructureToThickeningIdeal f t n m =
      (Modules.unitHomEquivTop _).symm m :=
  Hom.toPushforwardStructure_descPushforwardStructure _ _ _

/-- **The factorisation is unique**, because `𝒪_{W ×_T T_{n+1}} ⟶ (i₀)_* 𝒪_{W ×_T T₀}` is an
epimorphism. -/
lemma eq_pushforwardStructureToThickeningIdeal (m : Γ((thickeningIdeal f t n).toModules, ⊤))
    (χ : (Modules.pushforward (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)))).obj
        (infinitesimalBaseChange f t 0).structureModules ⟶ (thickeningIdeal f t n).toModules)
    (hχ : (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1))).toPushforwardStructure ≫ χ =
      (Modules.unitHomEquivTop _).symm m) :
    χ = pushforwardStructureToThickeningIdeal f t n m :=
  Hom.eq_descPushforwardStructure _ _ _ _ hχ

/-- **The comparison morphism `(i₀)_* (𝒪_{W ×_T T₀}^ι) ⟶ Iₙ` attached to a family `m` of global
sections of the thickening ideal**: on the `j`-th summand it is multiplication by `m j`.

The source is a pushforward, so the morphism cannot be written down on sections; it is
assembled from the family by
`AlgebraicGeometry.Scheme.Modules.pushforwardFreeDesc`, which uses that
`Modules.pushforward` is additive and therefore turns the free module `𝒪_{W ×_T T₀}^ι` into a
coproduct of `ι` copies of `(i₀)_* 𝒪_{W ×_T T₀}`.

When the classes of the `m j` form a basis of `Iₙ / 𝔪 Iₙ` over the residue field this morphism
is an isomorphism. -/
noncomputable def pushforwardFreeToThickeningIdeal {ι : Type u} [Finite ι]
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)) :
    (Modules.pushforward (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)))).obj
        ((infinitesimalBaseChange f t 0).freeModules ι) ⟶ (thickeningIdeal f t n).toModules :=
  Modules.pushforwardFreeDesc _ fun j ↦ pushforwardStructureToThickeningIdeal f t n (m j)

/-- **On the `j`-th summand the comparison morphism is multiplication by `m j`.** -/
@[reassoc (attr := simp)]
lemma map_ιFree_comp_pushforwardFreeToThickeningIdeal {ι : Type u} [Finite ι]
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤)) (j : ι) :
    (Modules.pushforward (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)))).map
        (SheafOfModules.ιFree j) ≫ pushforwardFreeToThickeningIdeal f t n m =
      pushforwardStructureToThickeningIdeal f t n (m j) :=
  Modules.map_ιFree_comp_pushforwardFreeDesc _ _ _

/-- **The comparison morphism is the only one that is multiplication by `m j` on the `j`-th
summand.** -/
lemma eq_pushforwardFreeToThickeningIdeal {ι : Type u} [Finite ι]
    (m : ι → Γ((thickeningIdeal f t n).toModules, ⊤))
    (χ : (Modules.pushforward (infinitesimalBaseChangeMap f t (Nat.zero_le (n + 1)))).obj
        ((infinitesimalBaseChange f t 0).freeModules ι) ⟶ (thickeningIdeal f t n).toModules)
    (hχ : ∀ j : ι, (Modules.pushforward (infinitesimalBaseChangeMap f t
        (Nat.zero_le (n + 1)))).map (SheafOfModules.ιFree j) ≫ χ =
      pushforwardStructureToThickeningIdeal f t n (m j)) :
    χ = pushforwardFreeToThickeningIdeal f t n m :=
  Modules.eq_pushforwardFreeDesc _ _ _ hχ

end Free

end AlgebraicGeometry.Scheme
