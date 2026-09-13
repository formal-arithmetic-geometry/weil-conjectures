/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero
public import WeilConjectures.AlgebraicGeometry.Cohomology.Thickening
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.Mathlib.AlgebraicGeometry.Stalk

/-!
# The theorem of the cube: triviality over the infinitesimal neighbourhoods

Let `X`, `Y` and `Z` be schemes over a base `S`, with sections `x₀`, `y₀`, `z₀` of their
structure morphisms, and let `L` be a line bundle on the triple product `(X ×_S Y) ×_S Z`
whose restrictions to the three slices

`(X ×_S Y) × {z₀}`,   `{x₀} × Y × Z`,   `X × {y₀} × Z`

are trivial. Writing `W := X ×_S Y` and `Zₙ` for the `n`-th infinitesimal neighbourhood of a
point `t` of `Z`, the theorem of the cube begins by showing that the pullback of `L` to
`W ×_Z Zₙ` is trivial for every `n`. That is `lem:cube-thickening-trivial` of the blueprint
(`27_theorem_of_the_cube.tex`), and it is what this file proves, by induction along the tower

```
  W ×_Z Z₀ ↪ W ×_Z Z₁ ↪ ⋯ ↪ W ×_Z Zₙ ↪ W ×_Z Z_{n+1} ↪ ⋯
```

whose steps are the square-zero thickenings of
`WeilConjectures.AlgebraicGeometry.Cohomology.Thickening`.

The induction step runs the five-term sequence of the step `W ×_Z Zₙ ↪ W ×_Z Z_{n+1}`
(`prop:cube-picard-square-zero`, in
`WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero`). Exactness at `Pic` produces
an obstruction class `α ∈ H¹(W ×_Z Z_{n+1}, Iₙ)` whose image is the class of the pullback of
`L`; the naturality ladder against the two slices kills both Künneth components of `α`; and
`α = 0` then says that the pullback of `L` is trivial.

## Main statements

- `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_succ_eq_one` — the induction
  step, for an arbitrary morphism `V ⟶ Z` with two slices `VX, VY ⟶ V` over `Z`.
- `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one` — the induction itself.
- `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one`
  (blueprint: `lem:cube-thickening-trivial`) — the specialisation to the triple product of the
  cube.
- `AlgebraicGeometry.Scheme.surjective_unitsMap_subschemeι_thickeningIdeal_pullbackSnd` — the
  unit-extension input `hX`, `hY` above, for a proper geometrically integral variety `X` over a
  field `k` and an arbitrary `k`-scheme `Z`.

## Implementation notes

* Two inputs of the blueprint's induction step are **hypotheses** of the statements here
  rather than theorems, because each is a self-contained piece of work of its own:
  - `hX`, `hY`: that `Γ(VX ×_Z Z_{n+1}, 𝒪)ˣ ⟶ Γ(VX ×_Z Zₙ, 𝒪)ˣ` is surjective, and likewise
    for `VY`. In the blueprint this is the surjection `Aₙ₊₁^× ⟶ Aₙ^×` of the local artinian
    rings, obtained from `lem:cube-global-sections-base-change` together with
    `Γ(𝒪^×) = Γ(𝒪)^×`. It is discharged in the case the cube needs by the last section of
    this file.
  - `hkunneth`: that a deformation class on `V ×_Z Z_{n+1}` restricting to zero on both
    slices is zero. In the blueprint this is three things together: `prop:cube-kunneth-h1`,
    the identification of the ideal of the thickening with `𝒪_W ⊗_k Iₙ` and hence of its `H¹`
    with `H¹(W, 𝒪_W) ⊗_k Iₙ`, and the invariance of `H¹` under pushforward along
    `W ×_Z Z₀ ↪ W ×_Z Z_{n+1}`.
  Everything else in the blueprint's proof is proved here. Because the blueprint's hypotheses
  on `X`, `Y` and `Z` (properness, the variety hypothesis, noetherianness, the base field)
  enter only through these two inputs, the statements below hold over an arbitrary base
  scheme `S`.
* The base point of the tower is a point `t` of `Z`, not the section `z₀`; the hypothesis
  `ht` relating the two says exactly that `t` is the point `z₀` picks out, in the form in
  which the argument uses it. For a rational point of a scheme over a field it is discharged
  by `AlgebraicGeometry.Scheme.fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id`.
* The statements are `Pic`-theoretic: "the pullback of `L` is trivial" is
  `AlgebraicGeometry.Scheme.Pic.map _ (Scheme.Pic.mk L hL) = 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-! ### The induction -/

section Deformation

variable {Z V VX VY : Scheme.{u}} (p : V ⟶ Z) (pX : VX ⟶ Z) (pY : VY ⟶ Z)
  (uX : VX ⟶ V) (huX : uX ≫ p = pX) (uY : VY ⟶ V) (huY : uY ≫ p = pY) (t : Z)

/-- **The inductive step of `lem:cube-thickening-trivial`.**

Let `V ⟶ Z` be a morphism with two "slices" `uX : VX ⟶ V` and `uY : VY ⟶ V` over `Z`, let `t`
be a point of `Z` and let `M` be a line bundle on `V` trivial on both slices. Assume that the
units of the `n`-th infinitesimal thickenings of `VX` and `VY` extend (`hX`, `hY`) and that a
deformation class on `V ×_Z Z_{n+1}` vanishing on both slices vanishes (`hkunneth`). Then
triviality of the pullback of `M` to `V ×_Z Zₙ` propagates to `V ×_Z Z_{n+1}`. -/
theorem Pic.map_infinitesimalBaseChangeFst_succ_eq_one (n : ℕ)
    (hX : Function.Surjective (Hom.unitsMap (thickeningIdeal pX t n).subschemeι))
    (hY : Function.Surjective (Hom.unitsMap (thickeningIdeal pY t n).subschemeι))
    (hkunneth : Function.Injective
      ((thickeningH1Map p pX uX huX t n).prod (thickeningH1Map p pY uY huY t n)))
    {M : V.Modules} (hM : M.Invertible)
    (hMX : Pic.map uX (Pic.mk M hM) = 1) (hMY : Pic.map uY (Pic.mk M hM) = 1)
    (hn : Pic.map (infinitesimalBaseChangeFst p t n) (Pic.mk M hM) = 1) :
    Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) = 1 := by
  have hI : thickeningIdeal p t n ^ 2 = 0 := sq_thickeningIdeal p t n
  -- the class of `M` pulled back to `V ×_Z Z_{n+1}` dies on `V ×_Z Zₙ`
  have hc : Pic.map (thickeningIdeal p t n).subschemeι
      (Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM)) = 1 := by
    rw [← Pic.map_comp_apply, ← thickeningIso_inv_infinitesimalBaseChangeMap, Category.assoc,
      infinitesimalBaseChangeMap_fst, Pic.map_comp_apply, hn, map_one]
  -- the obstruction class
  obtain ⟨α, hα⟩ : Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) ∈
      ((thickeningIdeal p t n).h1ToPic hI).range := by
    rwa [IdealSheafData.range_h1ToPic_eq_ker _ hI]
  -- both of its slice components vanish, hence so does it
  have hαX := thickeningH1Map_eq_one_of_pic_map_eq_one p pX uX huX t n hX hM hMX α hα
  have hαY := thickeningH1Map_eq_one_of_pic_map_eq_one p pY uY huY t n hY hM hMY α hα
  have hα1 : α = 1 := hkunneth (a₁ := α) (a₂ := 1) (by simp [hαX, hαY])
  rw [← hα, hα1, map_one]

/-- **Triviality over all the infinitesimal neighbourhoods**, the inductive core of
`lem:cube-thickening-trivial`: under the hypotheses of
`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_succ_eq_one` for every `n`, a
line bundle on `V` that is trivial on the two slices and on `V ×_Z Z₀` is trivial on
`V ×_Z Zₙ` for every `n`. -/
theorem Pic.map_infinitesimalBaseChangeFst_eq_one
    (hX : ∀ n, Function.Surjective (Hom.unitsMap (thickeningIdeal pX t n).subschemeι))
    (hY : ∀ n, Function.Surjective (Hom.unitsMap (thickeningIdeal pY t n).subschemeι))
    (hkunneth : ∀ n, Function.Injective
      ((thickeningH1Map p pX uX huX t n).prod (thickeningH1Map p pY uY huY t n)))
    {M : V.Modules} (hM : M.Invertible)
    (hMX : Pic.map uX (Pic.mk M hM) = 1) (hMY : Pic.map uY (Pic.mk M hM) = 1)
    (h0 : Pic.map (infinitesimalBaseChangeFst p t 0) (Pic.mk M hM) = 1) (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst p t n) (Pic.mk M hM) = 1 := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact Pic.map_infinitesimalBaseChangeFst_succ_eq_one p pX pY uX huX uY huY t n
        (hX n) (hY n) (hkunneth n) hM hMX hMY ih

end Deformation

/-! ### The theorem of the cube: triviality over the infinitesimal neighbourhoods -/

section Cube

variable {S X Y Z : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S)

/-- **Triviality over the infinitesimal neighbourhoods** (blueprint:
`lem:cube-thickening-trivial`).

Let `X`, `Y` and `Z` be schemes over `S` with sections `x₀`, `y₀`, `z₀` of their structure
morphisms, let `t` be the point of `Z` picked out by `z₀` (in the form `ht`), and let `L` be a
line bundle on `(X ×_S Y) ×_S Z` whose restrictions to the three slices `(X ×_S Y) × {z₀}`,
`{x₀} × Y × Z` and `X × {y₀} × Z` are trivial. Then the pullback of `L` to
`((X ×_S Y) ×_S Z) ×_Z Zₙ` is trivial for every `n`.

The unit-extension input (`hX` for `X`, `hY` for `Y`) and the Künneth input (`hkunneth`),
which the blueprint proves from properness, the variety hypothesis and the Künneth formula,
are carried as hypotheses; see the implementation notes of this file. -/
theorem Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one
    (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S)
    (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ = Z.fromInfinitesimalNeighborhood t 0)
    (hX : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι))
    (hY : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πY πZ) t n).subschemeι))
    (hkunneth : ∀ n, Function.Injective
      ((thickeningH1Map (pullback.snd (pullback.fst πX πY ≫ πX) πZ) (pullback.snd πX πZ)
            (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀)
            (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) t n).prod
        (thickeningH1Map (pullback.snd (pullback.fst πX πY ≫ πX) πZ) (pullback.snd πY πZ)
            (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀)
            (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t n)))
    {L : (pullback (pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (pullback.fst πX πY ≫ πX) πZ z₀ hz₀) (Pic.mk L hL) = 1)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1)
    (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t n)
      (Pic.mk L hL) = 1 := by
  refine Pic.map_infinitesimalBaseChangeFst_eq_one _ _ _ _
    (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) _
    (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t hX hY hkunneth hL hLX hLY ?_ n
  rw [← infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst _ πZ z₀ hz₀ t ht,
    Pic.map_comp_apply, hLz, map_one]

end Cube

/-! ### Units of the thickenings of a proper variety -/

section Units

variable {K : Type u} [Field K] {X Z : Scheme.{u}}

/-- **The global sections of `(X ×_k Z) ×_Z Zₙ` are the infinitesimal ring `Aₙ`.**

For `X` a proper geometrically integral variety over a field `k`, `Z` a `k`-scheme and `t` a
point of `Z`, the `n`-th infinitesimal base change of `X ×_k Z ⟶ Z` along `Zₙ ⟶ Z` is
`X ×_k Spec Aₙ` with `Aₙ = 𝒪_{Z, t} ⧸ 𝔪_t ^ (n + 1)`, so its global sections are `Aₙ` by
`AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_snd_appTop` (blueprint:
`lem:cube-global-sections-base-change`). -/
theorem bijective_infinitesimalRingToΓ_pullbackSnd (πX : X ⟶ Spec (.of K)) [IsProper πX]
    [GeometricallyIntegral πX] (πZ : Z ⟶ Spec (.of K)) (t : Z) (n : ℕ) :
    Function.Bijective (infinitesimalRingToΓ (pullback.snd πX πZ) t n) := by
  set φ := Spec.preimage (Z.fromInfinitesimalNeighborhood t n ≫ πZ)
  have hφ : Z.fromInfinitesimalNeighborhood t n ≫ πZ = Spec.map φ := (Spec.map_preimage _).symm
  -- `(X ×_k Z) ×_Z Zₙ ≅ X ×_k Spec Aₙ`, by pasting the two cartesian squares
  have H := (IsPullback.of_hasPullback (pullback.snd πX πZ)
    (Z.fromInfinitesimalNeighborhood t n)).paste_horiz (IsPullback.of_hasPullback πX πZ)
  rw [hφ] at H
  have key : IsIso ((Scheme.ΓSpecIso (Z.infinitesimalRing t n)).inv ≫
      (pullback.snd πX (Spec.map φ)).appTop) := by
    let _ : Algebra K (Z.infinitesimalRing t n) := φ.hom.toAlgebra
    exact isIso_ΓSpecIso_inv_comp_snd_appTop πX (Z.infinitesimalRing t n)
  rw [← ConcreteCategory.isIso_iff_bijective, infinitesimalRingToΓ]
  change IsIso ((Scheme.ΓSpecIso (Z.infinitesimalRing t n)).inv ≫
    (pullback.snd (pullback.snd πX πZ) (Z.fromInfinitesimalNeighborhood t n)).appTop)
  rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_appTop, ← Category.assoc]
  infer_instance

/-- **Units of an infinitesimal thickening lift** (blueprint: the surjection `Aₙ₊₁^× ↠ Aₙ^×`
in the proof of `lem:cube-thickening-trivial`).

For `X` a proper geometrically integral variety over a field `k`, `Z` a `k`-scheme and `t` a
point of `Z`, every unit on the `n`-th infinitesimal thickening `(X ×_k Z) ×_Z Zₙ` extends to
the `(n + 1)`-st. This is the hypothesis `hX` (and, for `Y` in place of `X`, `hY`) of
`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one`.
-/
theorem surjective_unitsMap_subschemeι_thickeningIdeal_pullbackSnd (πX : X ⟶ Spec (.of K))
    [IsProper πX] [GeometricallyIntegral πX] (πZ : Z ⟶ Spec (.of K)) (t : Z) (n : ℕ) :
    Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι) := by
  intro y
  -- transport the problem along `(X ×_k Z) ×_Z Zₙ ≅ V(Iₙ)`
  have hcomp : (Hom.unitsMap (thickeningIso (pullback.snd πX πZ) t n).hom).comp
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι) =
      Hom.unitsMap (infinitesimalBaseChangeMap (pullback.snd πX πZ) t (Nat.le_succ n)) := by
    rw [← Hom.unitsMap_comp, thickeningIso_hom_subschemeι]
  have hinj : Function.Injective
      (Hom.unitsMap (thickeningIso (pullback.snd πX πZ) t n).hom) := by
    refine Function.LeftInverse.injective
      (g := Hom.unitsMap (thickeningIso (pullback.snd πX πZ) t n).inv) fun u ↦ ?_
    rw [← MonoidHom.comp_apply, ← Hom.unitsMap_comp, Iso.inv_hom_id, Hom.unitsMap_id,
      MonoidHom.id_apply]
  -- lift the unit through `Γ(- , 𝒪) = Aₙ`
  obtain ⟨b, hbu, hb⟩ := exists_isUnit_appTop_infinitesimalBaseChangeMap (pullback.snd πX πZ) t
    (Nat.le_succ n) (bijective_infinitesimalRingToΓ_pullbackSnd πX πZ t n)
    ((Hom.unitsMap (thickeningIso (pullback.snd πX πZ) t n).hom y).isUnit)
  refine ⟨hbu.unit, hinj ?_⟩
  rw [← MonoidHom.comp_apply, hcomp]
  exact Units.ext hb

end Units

end AlgebraicGeometry.Scheme
