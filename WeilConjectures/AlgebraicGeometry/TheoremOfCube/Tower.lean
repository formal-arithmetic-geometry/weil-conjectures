/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero
public import WeilConjectures.AlgebraicGeometry.Cohomology.Thickening
public import WeilConjectures.AlgebraicGeometry.ThickeningUnits
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

Everything below is in the namespace `AlgebraicGeometry.Scheme`.

- `Pic.map_infinitesimalBaseChangeFst_succ_eq_one` — the induction step, for an arbitrary
  morphism `V ⟶ Z` with two slices `VX, VY ⟶ V` over `Z`.
- `Pic.map_infinitesimalBaseChangeFst_eq_one` — the induction itself.
- `Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper` — the induction over a field, for
  proper geometrically integral varieties `X` and `Y` and an arbitrary point `t` of `Z`, where
  the unit-extension input is a theorem rather than a hypothesis and the base case is asked on
  the fibre over `t`. This is the form the theorem of the cube consumes.
- `Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one` and
  `Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one_of_isProper`
  (blueprint: `lem:cube-thickening-trivial`) — the same two statements at the point picked out
  by a section `z₀` of `πZ`, with the base case asked in the form of the slice
  `X × Y × {z₀}`.

`AlgebraicGeometry.Scheme.IsCubeKunneth` names the Künneth input, which all of these carry as
a hypothesis.

## Implementation notes

* Two inputs of the blueprint's induction step are **hypotheses** of the statements here
  rather than theorems, because each is a self-contained piece of work of its own:
  - `hX`, `hY`: that `Γ(VX ×_Z Z_{n+1}, 𝒪)ˣ ⟶ Γ(VX ×_Z Zₙ, 𝒪)ˣ` is surjective, and likewise
    for `VY`. In the blueprint this is the surjection `Aₙ₊₁^× ⟶ Aₙ^×` of the local artinian
    rings, obtained from `lem:cube-global-sections-base-change` together with
    `Γ(𝒪^×) = Γ(𝒪)^×`. For proper varieties over a field it is discharged by
    `AlgebraicGeometry.Scheme.unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective`, in
    `WeilConjectures.AlgebraicGeometry.ThickeningUnits`; this is what the `_of_isProper`
    statements below do.
  - `hkunneth`: that a deformation class on `V ×_Z Z_{n+1}` restricting to zero on both
    slices is zero. In the blueprint this is three things together: `prop:cube-kunneth-h1`,
    the identification of the ideal of the thickening with `𝒪_W ⊗_k Iₙ` and hence of its `H¹`
    with `H¹(W, 𝒪_W) ⊗_k Iₙ`, and the invariance of `H¹` under pushforward along
    `W ×_Z Z₀ ↪ W ×_Z Z_{n+1}`. For the triple product of the cube it is spelled once, as
    `AlgebraicGeometry.Scheme.IsCubeKunneth`, so that the statements that carry it and the
    statement that will one day discharge it are literally the same condition.
  Everything else in the blueprint's proof is proved here. Because the blueprint's hypotheses
  on `X`, `Y` and `Z` (properness, the variety hypothesis, noetherianness, the base field)
  enter only through these two inputs, the statements below hold over an arbitrary base
  scheme `S`.
* The base point of the tower is a point `t` of `Z`, not the section `z₀`; the hypothesis
  `ht` relating the two says exactly that `t` is the point `z₀` picks out, in the form in
  which the argument uses it. For a rational point of a scheme over a field it is discharged
  by `AlgebraicGeometry.Scheme.fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id`. The
  passage from the slice `X × Y × {z₀}` to the base case of the induction is
  `AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_zero_eq_one_of_sliceInclusionFst`,
  which is stated here rather than beside the commuting triangle it uses,
  `AlgebraicGeometry.Scheme.infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst`, because
  that lives in the Mathlib mirror `WeilConjectures.Mathlib.AlgebraicGeometry.Stalk` and `Pic`
  is a construction of this project.
* The statements are `Pic`-theoretic: "the pullback of `L` is trivial" is
  `AlgebraicGeometry.Scheme.Pic.map _ (Scheme.Pic.mk L hL) = 1`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing Limits

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

/-! ### The base case at a section of the structure morphism -/

section BaseCase

variable {S Z V : Scheme.{u}} (πV : V ⟶ S) (πZ : Z ⟶ S)

/-- **Triviality on the slice through a section is triviality on the zeroth infinitesimal
neighbourhood of the point it picks out.** This is the base case of the induction, in the form
in which the blueprint asks for it. It is the commuting triangle
`AlgebraicGeometry.Scheme.infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst` read through
the functoriality of `AlgebraicGeometry.Scheme.Pic.map`. -/
theorem Pic.map_infinitesimalBaseChangeFst_zero_eq_one_of_sliceInclusionFst
    (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ = Z.fromInfinitesimalNeighborhood t 0)
    {L : (pullback πV πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst πV πZ z₀ hz₀) (Pic.mk L hL) = 1) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0) (Pic.mk L hL) = 1 := by
  rw [← infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst πV πZ z₀ hz₀ t ht,
    Pic.map_comp_apply, hLz, map_one]

end BaseCase

/-! ### The theorem of the cube: triviality over the infinitesimal neighbourhoods -/

section Cube

variable {S X Y Z : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S)

/-- **The Künneth input to the theorem of the cube**, at a point `t` of `Z` and at level `n`:
a deformation class on `((X ×_S Y) ×_S Z) ×_Z Z_{n+1}` whose restrictions to the two slices
`{x₀} × Y × Z` and `X × {y₀} × Z` both vanish is itself zero.

This is the hypothesis `hkunneth` of
`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_succ_eq_one` specialised to the
triple product of the cube. It is given a name because every statement of the cube carries it
as a hypothesis rather than discharging it; see the implementation notes of this file for what
it is in the blueprint. -/
def IsCubeKunneth (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S)
    (t : Z) (n : ℕ) : Prop :=
  Function.Injective
    ((thickeningH1Map (pullback.snd (pullback.fst πX πY ≫ πX) πZ) (pullback.snd πX πZ)
          (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀)
          (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) t n).prod
      (thickeningH1Map (pullback.snd (pullback.fst πX πY ≫ πX) πZ) (pullback.snd πY πZ)
          (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀)
          (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t n))

/-- **Triviality over the infinitesimal neighbourhoods** (blueprint:
`lem:cube-thickening-trivial`).

Let `X`, `Y` and `Z` be schemes over `S` with sections `x₀`, `y₀`, `z₀` of their structure
morphisms, let `t` be the point of `Z` picked out by `z₀` (in the form `ht`), and let `L` be a
line bundle on `(X ×_S Y) ×_S Z` whose restrictions to the three slices `(X ×_S Y) × {z₀}`,
`{x₀} × Y × Z` and `X × {y₀} × Z` are trivial. Then the pullback of `L` to
`((X ×_S Y) ×_S Z) ×_Z Zₙ` is trivial for every `n`.

The unit-extension input (`hX` for `X`, `hY` for `Y`) and the Künneth input (`hkunneth`),
which the blueprint proves from properness, the variety hypothesis and the Künneth formula,
are carried as hypotheses; see the implementation notes of this file.

This is the form in which the blueprint states `lem:cube-thickening-trivial`, and it is stated
for the blueprint. The theorem of the cube itself goes through
`AlgebraicGeometry.Scheme.Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper`, which asks
for the base case on the fibre over `t` and so needs no section `z₀`. -/
theorem Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one
    (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S)
    (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ = Z.fromInfinitesimalNeighborhood t 0)
    (hX : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι))
    (hY : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πY πZ) t n).subschemeι))
    (hkunneth : ∀ n, IsCubeKunneth πX πY πZ x₀ hx₀ y₀ hy₀ t n)
    {L : (pullback (pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (pullback.fst πX πY ≫ πX) πZ z₀ hz₀) (Pic.mk L hL) = 1)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1)
    (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t n)
      (Pic.mk L hL) = 1 :=
  Pic.map_infinitesimalBaseChangeFst_eq_one _ _ _ _
    (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) _
    (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t hX hY hkunneth hL hLX hLY
    (Pic.map_infinitesimalBaseChangeFst_zero_eq_one_of_sliceInclusionFst _ πZ z₀ hz₀ t ht hL hLz)
    n

end Cube

/-! ### The theorem of the cube over a field -/

section Variety

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}}

/-- **Triviality over the infinitesimal neighbourhoods at an arbitrary point of `Z`**, for
proper varieties over a field.

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be an
arbitrary `K`-scheme, let `t` be an arbitrary point of `Z` and let `L` be a line bundle on
`(X ×_K Y) ×_K Z` trivial on the two slices `{x₀} × Y × Z` and `X × {y₀} × Z` and on the fibre
over `t` (`hL0`). Then the pullback of `L` to `((X ×_K Y) ×_K Z) ×_Z Zₙ` is trivial for every
`n`.

The base case `hL0` is asked on the zeroth infinitesimal base change, that is on the fibre over
`t`; unlike in
`Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one_of_isProper` below, in the
same namespace, it is not asked in the form of a slice through a rational point of `Z`, and `t`
accordingly need not be a rational point. -/
theorem Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper
    (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
    (πY : Y ⟶ Spec (.of K)) [IsProper πY] [GeometricallyIntegral πY] (πZ : Z ⟶ Spec (.of K))
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _) (t : Z)
    (hkunneth : ∀ n, IsCubeKunneth πX πY πZ x₀ hx₀ y₀ hy₀ t n)
    {L : (pullback (pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1)
    (hL0 : Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t 0)
      (Pic.mk L hL) = 1) (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t n)
      (Pic.mk L hL) = 1 :=
  Pic.map_infinitesimalBaseChangeFst_eq_one _ _ _ _
    (pullbackMapSliceInclusionFst_snd πX πY πZ y₀ hy₀) _
    (pullbackMapSliceInclusionSnd_snd πX πY πZ x₀ hx₀) t
    (unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective πX πZ t)
    (unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective πY πZ t)
    hkunneth hL hLX hLY hL0 n

/-- **Triviality over the infinitesimal neighbourhoods, for proper varieties over a field**
(blueprint: `lem:cube-thickening-trivial`).

Let `X` and `Y` be proper geometrically integral varieties over a field `K`, let `Z` be an
arbitrary `K`-scheme with a rational point `z₀`, and let `L` be a line bundle on
`(X ×_K Y) ×_K Z` trivial on the three slices `X × Y × {z₀}`, `{x₀} × Y × Z` and
`X × {y₀} × Z`. Then the pullback of `L` to `((X ×_K Y) ×_K Z) ×_Z Zₙ` is trivial for every
`n`, where `Zₙ` is the `n`-th infinitesimal neighbourhood of the point `z₀` picks out.

This is the blueprint's `lem:cube-thickening-trivial` over a field: the unit-extension
hypotheses are discharged by
`AlgebraicGeometry.Scheme.unitsMap_subschemeι_thickeningIdeal_pullbackSnd_surjective`, leaving
the Künneth input `hkunneth` as the only hypothesis of the blueprint's proof that is not yet a
theorem. -/
theorem Pic.map_infinitesimalBaseChangeFst_pullbackMapSliceInclusion_eq_one_of_isProper
    (πX : X ⟶ Spec (.of K)) [IsProper πX] [GeometricallyIntegral πX]
    (πY : Y ⟶ Spec (.of K)) [IsProper πY] [GeometricallyIntegral πY] (πZ : Z ⟶ Spec (.of K))
    (x₀ : Spec (.of K) ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 _)
    (y₀ : Spec (.of K) ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 _)
    (z₀ : Spec (.of K) ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 _)
    (hkunneth : ∀ n, IsCubeKunneth πX πY πZ x₀ hx₀ y₀ hy₀ (z₀ (closedPoint K)) n)
    {L : (pullback (pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (pullback.fst πX πY ≫ πX) πZ z₀ hz₀) (Pic.mk L hL) = 1)
    (hLX : Pic.map (pullbackMapSliceInclusionFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (pullbackMapSliceInclusionSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1)
    (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ)
      (z₀ (closedPoint K)) n) (Pic.mk L hL) = 1 :=
  Pic.map_infinitesimalBaseChangeFst_eq_one_of_isProper πX πY πZ x₀ hx₀ y₀ hy₀ _ hkunneth hL
    hLX hLY (Pic.map_infinitesimalBaseChangeFst_zero_eq_one_of_sliceInclusionFst _ πZ z₀ hz₀ _
      (fromInfinitesimalNeighborhood_zero_comp_of_comp_eq_id Z K πZ z₀ hz₀) hL hLz) n

end Variety

end AlgebraicGeometry.Scheme
