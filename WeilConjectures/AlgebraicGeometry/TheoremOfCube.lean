/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Kunneth
public import WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero
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
(`27_theorem_of_the_cube.tex`), and it is what this file proves, by induction on `n`.

The induction step runs the five-term sequence of the square-zero thickening
`W ×_Z Zₙ ↪ W ×_Z Z_{n+1}` (`prop:cube-picard-square-zero`, in
`WeilConjectures.AlgebraicGeometry.Cohomology.PicardSquareZero`). Exactness at `Pic` produces
an obstruction class `α ∈ H¹(W ×_Z Z_{n+1}, Iₙ)` whose image is the class of the pullback of
`L`; the naturality ladder against the two slices kills both Künneth components of `α`; and
`α = 0` then says that the pullback of `L` is trivial.

## Main statements

- `AlgebraicGeometry.pic_map_infinitesimalBaseChangeFst_succ_eq_one` — the induction step, for
  an arbitrary morphism `V ⟶ Z` with two slices `VX, VY ⟶ V` over `Z`.
- `AlgebraicGeometry.pic_map_infinitesimalBaseChangeFst_eq_one` — the induction itself.
- `AlgebraicGeometry.pic_map_cube_infinitesimalBaseChangeFst_eq_one` (blueprint:
  `lem:cube-thickening-trivial`) — the specialisation to the triple product of the cube.

## Implementation notes

* Two inputs of the blueprint's induction step are **hypotheses** of the statements here
  rather than theorems, because each is a self-contained piece of work of its own:
  - `hX`, `hY`: that `Γ(VX ×_Z Z_{n+1}, 𝒪)ˣ ⟶ Γ(VX ×_Z Zₙ, 𝒪)ˣ` is surjective, and likewise
    for `VY`. In the blueprint this is the surjection `Aₙ₊₁^× ⟶ Aₙ^×` of the local artinian
    rings, obtained from `lem:cube-global-sections-base-change` together with
    `Γ(𝒪^×) = Γ(𝒪)^×`.
  - `hkunneth`: that a deformation class on `W ×_Z Z_{n+1}` restricting to zero on both
    slices is zero. In the blueprint this is `prop:cube-kunneth-h1` tensored with the
    finite-dimensional vector space `Iₙ`, which needs the identification of the ideal of the
    thickening with `𝒪_W ⊗_k Iₙ` and of its `H¹` with `H¹(W, 𝒪_W) ⊗_k Iₙ`.
  Everything else in the blueprint's proof is proved here.
* The base point of the tower is a point `t` of `Z`, not the section `z₀`; the hypothesis
  `ht` relating the two says exactly that `t` is the point `z₀` picks out, in the form in
  which the argument uses it.
* The statements are `Pic`-theoretic: "the pullback of `L` is trivial" is
  `AlgebraicGeometry.Scheme.Pic.map _ (Scheme.Pic.mk L hL) = 1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ### The comparison morphism of thickening ideals -/

variable {Z V V' : Scheme.{u}} (p : V ⟶ Z) (p' : V' ⟶ Z) (u : V' ⟶ V) (hu : u ≫ p = p') (t : Z)

/-- **The comparison morphism of thickening ideals** attached to a morphism `u : V' ⟶ V` over
`Z`: the factorisation of the pullback of the ideal of `V ×_Z Zₙ ↪ V ×_Z Z_{n+1}` through the
ideal of `V' ×_Z Zₙ ↪ V' ×_Z Z_{n+1}`. -/
noncomputable def thickeningComparison (n : ℕ) :
    (Modules.pullback (infinitesimalBaseChangeMapOver p p' u hu t (n + 1))).obj
        (thickeningIdeal p t n).toModules ⟶ (thickeningIdeal p' t n).toModules :=
  IdealSheafData.comapModulesMap _ _ _ (comap_thickeningIdeal_le p p' u hu t n)

/-- The map on deformation classes `H¹(V ×_Z Z_{n+1}, Iₙ) ⟶ H¹(V' ×_Z Z_{n+1}, I'ₙ)` induced
by a morphism `u : V' ⟶ V` over `Z`. This is the middle vertical map of the naturality ladder
of `prop:cube-picard-square-zero`. -/
noncomputable def thickeningH1Map (n : ℕ) :
    Multiplicative ((thickeningIdeal p t n).toModules.H 1) →*
      Multiplicative ((thickeningIdeal p' t n).toModules.H 1) :=
  IdealSheafData.h1Map _ _ (infinitesimalBaseChangeMapOver p p' u hu t (n + 1))
    (thickeningComparison p p' u hu t n)

end Scheme

/-! ### The inductive step -/

section Deformation

open Scheme

variable {Z V VX VY : Scheme.{u}} (p : V ⟶ Z) (pX : VX ⟶ Z) (pY : VY ⟶ Z)
  (uX : VX ⟶ V) (huX : uX ≫ p = pX) (uY : VY ⟶ V) (huY : uY ≫ p = pY) (t : Z)

/-- **The inductive step of `lem:cube-thickening-trivial`.**

Let `V ⟶ Z` be a morphism with two "slices" `uX : VX ⟶ V` and `uY : VY ⟶ V` over `Z`, let `t`
be a point of `Z` and let `M` be a line bundle on `V` trivial on both slices. Assume that the
units of the `n`-th infinitesimal thickenings of `VX` and `VY` extend
(`hX`, `hY`) and that a deformation class on `V ×_Z Z_{n+1}` vanishing on both slices vanishes
(`hkunneth` — this is `prop:cube-kunneth-h1` tensored with `Iₙ`). Then triviality of the
pullback of `M` to `V ×_Z Zₙ` propagates to `V ×_Z Z_{n+1}`. -/
theorem pic_map_infinitesimalBaseChangeFst_succ_eq_one (n : ℕ)
    (hX : Function.Surjective (Hom.unitsMap (thickeningIdeal pX t n).subschemeι))
    (hY : Function.Surjective (Hom.unitsMap (thickeningIdeal pY t n).subschemeι))
    (hkunneth : ∀ α : Multiplicative ((thickeningIdeal p t n).toModules.H 1),
      thickeningH1Map p pX uX huX t n α = 1 → thickeningH1Map p pY uY huY t n α = 1 → α = 1)
    {M : V.Modules} (hM : M.Invertible)
    (hMX : Pic.map uX (Pic.mk M hM) = 1) (hMY : Pic.map uY (Pic.mk M hM) = 1)
    (hn : Pic.map (infinitesimalBaseChangeFst p t n) (Pic.mk M hM) = 1) :
    Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) = 1 := by
  have hI : thickeningIdeal p t n ^ 2 = 0 := sq_thickeningIdeal p t n
  have hsub : (thickeningIdeal p t n).subschemeι =
      (thickeningIso p t n).inv ≫ infinitesimalBaseChangeMap p t (Nat.le_succ n) := by
    rw [← thickeningIso_hom_subschemeι p t n, Iso.inv_hom_id_assoc]
  -- the class of `M` pulled back to `V ×_Z Z_{n+1}` dies on `V ×_Z Zₙ`
  have hc : Pic.map (thickeningIdeal p t n).subschemeι
      (Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM)) = 1 := by
    have h1 : Pic.map (thickeningIdeal p t n).subschemeι
        (Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM)) =
        Pic.map ((thickeningIdeal p t n).subschemeι ≫
          infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) := by
      rw [Pic.map_comp]; rfl
    rw [h1, hsub, Category.assoc, infinitesimalBaseChangeMap_fst, Pic.map_comp,
      MonoidHom.comp_apply, hn, map_one]
  -- the obstruction class
  obtain ⟨α, hα⟩ : Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) ∈
      ((thickeningIdeal p t n).h1ToPic hI).range := by
    rw [IdealSheafData.range_h1ToPic_eq_ker _ hI]
    exact hc
  -- its two slice components vanish
  have key : ∀ {V' : Scheme.{u}} (p' : V' ⟶ Z) (u : V' ⟶ V) (hu : u ≫ p = p'),
      Pic.map u (Pic.mk M hM) = 1 →
      Function.Surjective (Hom.unitsMap (thickeningIdeal p' t n).subschemeι) →
      thickeningH1Map p p' u hu t n α = 1 := by
    intro V' p' u hu hMu hu'
    refine IdealSheafData.injective_h1ToPic _ (sq_thickeningIdeal p' t n) hu' ?_
    rw [map_one]
    have hnat := IdealSheafData.h1ToPic_naturality (thickeningIdeal p t n)
      (thickeningIdeal p' t n) (infinitesimalBaseChangeMapOver p p' u hu t (n + 1))
      (thickeningComparison p p' u hu t n) hI (sq_thickeningIdeal p' t n)
      (IdealSheafData.comapModulesMap_toModulesι _ _ _ _).symm
    have := congrArg (fun f : Multiplicative ((thickeningIdeal p t n).toModules.H 1) →*
      _ => f α) hnat
    simp only [MonoidHom.comp_apply] at this
    simp only [thickeningH1Map]
    rw [← this, hα]
    have h2 : Pic.map (infinitesimalBaseChangeMapOver p p' u hu t (n + 1))
        (Pic.map (infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM)) =
        Pic.map (infinitesimalBaseChangeMapOver p p' u hu t (n + 1) ≫
          infinitesimalBaseChangeFst p t (n + 1)) (Pic.mk M hM) := by
      rw [Pic.map_comp]; rfl
    rw [h2, infinitesimalBaseChangeMapOver_fst, Pic.map_comp, MonoidHom.comp_apply, hMu, map_one]
  rw [← hα, hkunneth α (key pX uX huX hMX hX) (key pY uY huY hMY hY), map_one]

end Deformation


section Deformation

open Scheme

variable {Z V VX VY : Scheme.{u}} (p : V ⟶ Z) (pX : VX ⟶ Z) (pY : VY ⟶ Z)
  (uX : VX ⟶ V) (huX : uX ≫ p = pX) (uY : VY ⟶ V) (huY : uY ≫ p = pY) (t : Z)

/-- **Triviality over all the infinitesimal neighbourhoods**, the inductive core of
`lem:cube-thickening-trivial`. -/
theorem pic_map_infinitesimalBaseChangeFst_eq_one
    (hX : ∀ n, Function.Surjective (Hom.unitsMap (thickeningIdeal pX t n).subschemeι))
    (hY : ∀ n, Function.Surjective (Hom.unitsMap (thickeningIdeal pY t n).subschemeι))
    (hkunneth : ∀ (n : ℕ) (α : Multiplicative ((thickeningIdeal p t n).toModules.H 1)),
      thickeningH1Map p pX uX huX t n α = 1 → thickeningH1Map p pY uY huY t n α = 1 → α = 1)
    {M : V.Modules} (hM : M.Invertible)
    (hMX : Pic.map uX (Pic.mk M hM) = 1) (hMY : Pic.map uY (Pic.mk M hM) = 1)
    {V₀ : Scheme.{u}} (j : V₀ ⟶ V) (w : infinitesimalBaseChange p t 0 ⟶ V₀)
    (hw : w ≫ j = infinitesimalBaseChangeFst p t 0) (hMj : Pic.map j (Pic.mk M hM) = 1)
    (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst p t n) (Pic.mk M hM) = 1 := by
  induction n with
  | zero => rw [← hw, Pic.map_comp, MonoidHom.comp_apply, hMj, map_one]
  | succ n ih =>
      exact pic_map_infinitesimalBaseChangeFst_succ_eq_one p pX pY uX huX uY huY t n
        (hX n) (hY n) (hkunneth n) hM hMX hMY ih

end Deformation


/-! ### The theorem of the cube: triviality over the infinitesimal neighbourhoods -/

section Cube

open Scheme

variable {S X Y Z : Scheme.{u}} (πX : X ⟶ S) (πY : Y ⟶ S) (πZ : Z ⟶ S)

/-- The slice `X ×_S Z ⟶ (X ×_S Y) ×_S Z` of the triple product at a section `y₀` of `πY`:
the slice inclusion `j_{y₀} : X ⟶ X ×_S Y` crossed with the identity of `Z`. -/
noncomputable def cubeSliceFst (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S) :
    pullback πX πZ ⟶ pullback (pullback.fst πX πY ≫ πX) πZ :=
  pullback.map πX πZ (pullback.fst πX πY ≫ πX) πZ (sliceInclusionFst πX πY y₀ hy₀) (𝟙 Z) (𝟙 S)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma cubeSliceFst_snd (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S) :
    cubeSliceFst πX πY πZ y₀ hy₀ ≫ pullback.snd (pullback.fst πX πY ≫ πX) πZ =
      pullback.snd πX πZ := by
  simp [cubeSliceFst]

/-- The slice `Y ×_S Z ⟶ (X ×_S Y) ×_S Z` of the triple product at a section `x₀` of `πX`:
the slice inclusion `j_{x₀} : Y ⟶ X ×_S Y` crossed with the identity of `Z`. -/
noncomputable def cubeSliceSnd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) :
    pullback πY πZ ⟶ pullback (pullback.fst πX πY ≫ πX) πZ :=
  pullback.map πY πZ (pullback.fst πX πY ≫ πX) πZ (sliceInclusionSnd πX πY x₀ hx₀) (𝟙 Z) (𝟙 S)
    (by simp [hx₀]) (by simp)

@[reassoc (attr := simp)]
lemma cubeSliceSnd_snd (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) :
    cubeSliceSnd πX πY πZ x₀ hx₀ ≫ pullback.snd (pullback.fst πX πY ≫ πX) πZ =
      pullback.snd πY πZ := by
  simp [cubeSliceSnd]

/-- The zeroth infinitesimal base change `(V ×_S Z) ×_Z Z₀ ⟶ V ×_S Z` factors through the slice
`V ⟶ V ×_S Z` at a section `z₀` of `πZ`, provided `t` is the point `z₀` in the precise sense
that `Z₀ ⟶ Z` is unchanged by `Z ⟶ S ⟶ Z`. -/
lemma infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst {S Z V : Scheme.{u}}
    (πV : V ⟶ S) (πZ : Z ⟶ S) (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ =
      Z.fromInfinitesimalNeighborhood t 0) :
    (infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 ≫ pullback.fst πV πZ) ≫
      sliceInclusionFst πV πZ z₀ hz₀ = infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 := by
  refine pullback.hom_ext (by simp) ?_
  have h1 : pullback.fst πV πZ ≫ πV = pullback.snd πV πZ ≫ πZ := pullback.condition
  have h2 : infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0 ≫ pullback.snd πV πZ =
      infinitesimalBaseChangeSnd (pullback.snd πV πZ) t 0 ≫
        Z.fromInfinitesimalNeighborhood t 0 := pullback.condition
  rw [Category.assoc, Category.assoc, sliceInclusionFst_snd,
    ← Category.assoc (pullback.fst πV πZ), h1, Category.assoc,
    ← Category.assoc (infinitesimalBaseChangeFst (pullback.snd πV πZ) t 0), h2, Category.assoc, ht]

/-- **Triviality over the infinitesimal neighbourhoods** (blueprint:
`lem:cube-thickening-trivial`), modulo its two remaining inputs `hX`, `hY` and `hkunneth`. -/
theorem pic_map_cube_infinitesimalBaseChangeFst_eq_one
    (x₀ : S ⟶ X) (hx₀ : x₀ ≫ πX = 𝟙 S) (y₀ : S ⟶ Y) (hy₀ : y₀ ≫ πY = 𝟙 S)
    (z₀ : S ⟶ Z) (hz₀ : z₀ ≫ πZ = 𝟙 S) (t : Z)
    (ht : Z.fromInfinitesimalNeighborhood t 0 ≫ πZ ≫ z₀ = Z.fromInfinitesimalNeighborhood t 0)
    (hX : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πX πZ) t n).subschemeι))
    (hY : ∀ n, Function.Surjective
      (Hom.unitsMap (thickeningIdeal (pullback.snd πY πZ) t n).subschemeι))
    (hkunneth : ∀ (n : ℕ) (α : Multiplicative
        ((thickeningIdeal (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t n).toModules.H 1)),
      thickeningH1Map _ _ (cubeSliceFst πX πY πZ y₀ hy₀)
          (cubeSliceFst_snd πX πY πZ y₀ hy₀) t n α = 1 →
      thickeningH1Map _ _ (cubeSliceSnd πX πY πZ x₀ hx₀)
          (cubeSliceSnd_snd πX πY πZ x₀ hx₀) t n α = 1 → α = 1)
    {L : (pullback (pullback.fst πX πY ≫ πX) πZ).Modules} (hL : L.Invertible)
    (hLz : Pic.map (sliceInclusionFst (pullback.fst πX πY ≫ πX) πZ z₀ hz₀) (Pic.mk L hL) = 1)
    (hLX : Pic.map (cubeSliceFst πX πY πZ y₀ hy₀) (Pic.mk L hL) = 1)
    (hLY : Pic.map (cubeSliceSnd πX πY πZ x₀ hx₀) (Pic.mk L hL) = 1)
    (n : ℕ) :
    Pic.map (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t n)
      (Pic.mk L hL) = 1 := by
  refine pic_map_infinitesimalBaseChangeFst_eq_one _ _ _ _ (cubeSliceFst_snd πX πY πZ y₀ hy₀)
    _ (cubeSliceSnd_snd πX πY πZ x₀ hx₀) t hX hY hkunneth hL hLX hLY
    (sliceInclusionFst (pullback.fst πX πY ≫ πX) πZ z₀ hz₀)
    (infinitesimalBaseChangeFst (pullback.snd (pullback.fst πX πY ≫ πX) πZ) t 0 ≫
      pullback.fst (pullback.fst πX πY ≫ πX) πZ)
    (infinitesimalBaseChangeFst_zero_comp_sliceInclusionFst _ πZ z₀ hz₀ t ht) hLz n

end Cube

end AlgebraicGeometry
