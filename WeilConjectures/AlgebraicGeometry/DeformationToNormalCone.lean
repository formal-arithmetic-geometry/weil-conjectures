/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.NormalBundle
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace

/-!
# Deformation to the normal cone of a section

For a smooth morphism `g : V ⟶ B` with a closed section `s : B ⟶ V`, the *deformation to the
normal cone of the section* is

`𝒟_s V = Bl_{s(B) × {0}} (V ×_B 𝔸¹_B) ∖ (strict transform of the closed fibre)`,

the blow-up of `V ×_B 𝔸¹_B` along `s(B) × {0}` with the strict transform of the fibre over
`t = 0` removed. It carries a morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with a section
`s̃ : 𝔸¹_B ⟶ 𝒟_s V`; the fibre of `(g̃, s̃)` over `t = 1` is `(g, s)` and the fibre over
`t = 0` is `(π_N, 0_N)`, so the deformation interpolates between a smooth morphism with a
section and a vector bundle with its zero section.

Equivalently `𝒟_s V = Spec_V (⨁_{r ∈ ℤ} I_s^r t^{-r})` is the extended Rees construction,
with `I_s^r = 𝒪_V` for `r ≤ 0`; inverting `t` gives `V × 𝔾_m` and setting `t = 0` gives the
normal cone.

## Implementation notes

The pinned Mathlib has no relative `Spec` of a quasi-coherent graded algebra and the project's
blow-up is not yet available along an arbitrary closed subscheme of a non-affine scheme, so the
deformation space cannot be constructed here. As for the normal cone in
`WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion`, it is carried as *data*: the
structure `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` bundles the deformation
space, the two structure morphisms and the clauses of `sk-lem-geometry`, and the
blueprint lemma is the statement that such a datum exists.

The punctured trivialisation `κ°` of `sk-lem-geometry` (3) — the identification of the
deformation over `𝔾_{m,B}` with `V ×_B 𝔾_{m,B}` — is a field. `𝔾_m` is not a Mathlib scheme,
so `𝔾_{m,B}` is carried as an open subscheme of `𝔸¹_B` whose underlying set is the complement of
the zero section, as in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

The structure is stated for an arbitrary normal cone datum `N`
(`AlgebraicGeometry.Scheme.Hom.NormalConeData`), so that the DNC invariance of
`WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation` is proved for every such datum. The
existence statement `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData` is about
the normal bundle actually attached to the section `s`, `N_s = V(s^* Ω_{V/B})`
(`AlgebraicGeometry.Scheme.Hom.sectionNormalCone`,
`WeilConjectures.AlgebraicGeometry.NormalBundle`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`: the deformation space `𝒟_s V`
  together with `g̃`, `s̃` and the properties characterising them.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

The deformation to the normal cone of a closed section `s` of a morphism `g : V ⟶ B` smooth of
pure relative dimension `d`, as data. Writing `𝔸¹_B = 𝔸(Fin 1; B)` with its zero and unit
sections `i₀`, `i₁`, the datum consists of the deformation space `𝒟_s V`, a morphism
`g̃ : 𝒟_s V ⟶ 𝔸¹_B` again smooth of relative dimension `d`, a section `s̃` of `g̃`, and the
identification of the two fibres:

```
  V ---ι₁---> 𝒟_s V <---ι₀--- N_s          B ---s---> V
  |             |              |           |          |
  g             g̃             π_N          ‖          g
  v             v              v           v          v
  B ---i₁---> 𝔸¹_B <---i₀---- B           B ---𝟙----> B
```

both squares cartesian, with `ι₁` carrying `s` to `s̃` and `ι₀` carrying `0_N` to `s̃`. Away
from `t = 0` the deformation is trivial: over the punctured line `𝔾_{m,B} ⊆ 𝔸¹_B`, the
complement of the zero section, there is a cartesian square

```
  V ×_B 𝔾_{m,B} ---κ°---> 𝒟_s V
        |                   |
       pr₂                  g̃
        v                   v
     𝔾_{m,B} -----------> 𝔸¹_B
```

identifying `g̃⁻¹(𝔾_{m,B})` with `V ×_B 𝔾_{m,B}` over `𝔾_{m,B}`, under which `s̃` is `s × 1`.

Étale-locally on `B` the deformation has coordinates (clauses (2), (4) and (5)): over a
surjective étale `v : B' ⟶ B`, an open neighbourhood of the section in the base change
`𝒟_s V ×_{𝔸¹_B} 𝔸¹_{B'}` maps étale to `𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}`, carrying the section to
the zero section (`exists_etale_coordinates`).

The datum is stated for an arbitrary normal cone datum `N`; the deformation to the normal cone
of `s` is the one with `N = N_s` the normal bundle of `s`
(`AlgebraicGeometry.Scheme.Hom.sectionNormalCone`).

In the purity conventions every scheme is separated of finite type over the base field, so
`g̃` and the coordinate chart are moreover separated and compactifiable, and every open
immersion is quasi-compact; this is recorded, compactifiability being what makes the dualizing
complexes defined.

Mathlib has neither the relative `Spec` of the extended Rees algebra nor a blow-up along an
arbitrary closed subscheme, so the datum cannot be constructed here; existence is
`AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`. -/
-- TODO(unify): sk-def-purity-conv
structure DeformationToNormalConeData (d : ℕ) (g : V ⟶ B) (s : B ⟶ V)
    (N : NormalConeData d s) where
  /-- The deformation space `𝒟_s V`. -/
  scheme : Scheme.{u}
  /-- The structure morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B`. -/
  proj : scheme ⟶ 𝔸(ULift.{u} (Fin 1); B)
  /-- The section `s̃ : 𝔸¹_B ⟶ 𝒟_s V` of `g̃`. -/
  sect : 𝔸(ULift.{u} (Fin 1); B) ⟶ scheme
  /-- `s̃` really is a section of `g̃`. -/
  sect_comp_proj : sect ≫ proj = 𝟙 _
  /-- `g̃` is again smooth of pure relative dimension `d`. -/
  smoothOfRelativeDimension_proj : SmoothOfRelativeDimension d proj
  /-- `g̃` is separated: in the purity conventions every scheme is separated of finite type
  over the base field. -/
  isSeparated_proj : IsSeparated proj
  /-- `g̃` is compactifiable, as every separated morphism of finite type between schemes of
  finite type over a field is (Nagata). This is what makes the dualizing complex `ω_{g̃}`,
  and with it the family object of the deformation, defined. -/
  hasCompactification_proj : HasCompactification proj
  /-- The inclusion `ι₁ : V ⟶ 𝒟_s V` of the fibre over `t = 1`. -/
  oneFibre : V ⟶ scheme
  /-- The fibre of `g̃` over the unit section is `g`. -/
  isPullback_oneFibre :
    IsPullback oneFibre g proj (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)
  /-- `ι₁` carries the section `s` to `s̃`. -/
  comp_oneFibre : s ≫ oneFibre = AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ sect
  /-- The inclusion `ι₀ : N_s ⟶ 𝒟_s V` of the fibre over `t = 0`. -/
  zeroFibre : N.scheme ⟶ scheme
  /-- The fibre of `g̃` over the zero section is the normal cone. -/
  isPullback_zeroFibre :
    IsPullback zeroFibre N.proj proj (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)
  /-- `ι₀` carries the zero section of the normal cone to `s̃`. -/
  comp_zeroFibre :
    N.zeroSection ≫ zeroFibre = AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ sect
  /-- The punctured line `𝔾_{m,B} ⊆ 𝔸¹_B`, as an open subscheme. -/
  puncturedLine : (𝔸(ULift.{u} (Fin 1); B)).Opens
  /-- The punctured line is the complement of the zero section. -/
  coe_puncturedLine : (puncturedLine : Set 𝔸(ULift.{u} (Fin 1); B)) =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ
  /-- The trivialisation `κ° : V ×_B 𝔾_{m,B} ⟶ 𝒟_s V` of the deformation away from `t = 0`. -/
  generic : pullback g (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) ⟶ scheme
  /-- Over `𝔾_{m,B}` the deformation is `V ×_B 𝔾_{m,B}`: the square formed by `κ°`, the
  projection to `𝔾_{m,B}`, `g̃` and the inclusion `𝔾_{m,B} ⊆ 𝔸¹_B` is cartesian. -/
  isPullback_generic : IsPullback generic (pullback.snd _ _) proj puncturedLine.ι
  /-- Over `𝔾_{m,B}` the section `s̃` is `s × 1` (clause (3)): its restriction to the punctured
  line is `κ° ∘ (s × 1)`, for the section `s × 1 : 𝔾_{m,B} ⟶ V ×_B 𝔾_{m,B}`. -/
  exists_sect_generic : ∃ σ : puncturedLine.toScheme ⟶
      pullback g (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B),
    σ ≫ pullback.fst _ _ = (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s ∧
      σ ≫ pullback.snd _ _ = 𝟙 _ ∧ σ ≫ generic = puncturedLine.ι ≫ sect
  /-- Clauses (2), (4) and (5): étale-local coordinates on the deformation. There are a
  separated surjective étale `v : B' ⟶ B` and, writing `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B` for its base change
  and `𝒟' = 𝒟_s V ×_{𝔸¹_B} 𝔸¹_{B'}` for the base change of the deformation (5), a quasi-compact
  open `j : W ⟶ 𝒟'` containing the base-changed section `σ` together with a quasi-compact
  étale `c : W ⟶ 𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}` carrying `σ` to the zero section. Here `c` is the
  chart `u_i = x_i / t` of the deformation of the standard pair `(𝔸^d_{B'} → B', 0)`, which is
  `𝔸^d_{B'} ×_{B'} 𝔸¹_{B'}` (4), for étale coordinates `x₁, …, x_d` of `(g, s)` over `B'` (2). -/
  exists_etale_coordinates : ∃ (B' : Scheme.{u}) (v : B' ⟶ B) (W : Scheme.{u})
      (j : W ⟶ pullback proj (AffineSpace.map (ULift.{u} (Fin 1)) v))
      (c : W ⟶ 𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); B')))
      (σ : 𝔸(ULift.{u} (Fin 1); B') ⟶ W),
    _root_.AlgebraicGeometry.Etale v ∧ Surjective v ∧ IsSeparated v ∧ IsOpenImmersion j ∧
      QuasiCompact j ∧ _root_.AlgebraicGeometry.Etale c ∧ QuasiCompact c ∧
      HasCompactification c ∧
      j ≫ pullback.snd _ _ =
        c ≫ 𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); B')) ↘ 𝔸(ULift.{u} (Fin 1); B') ∧
      σ ≫ j ≫ pullback.fst _ _ = AffineSpace.map (ULift.{u} (Fin 1)) v ≫ sect ∧
      σ ≫ c = AffineSpace.zeroSection (ULift.{u} (Fin d)) 𝔸(ULift.{u} (Fin 1); B')

attribute [instance] DeformationToNormalConeData.smoothOfRelativeDimension_proj
  DeformationToNormalConeData.isSeparated_proj
  DeformationToNormalConeData.hasCompactification_proj

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

**Existence of the deformation to the normal cone.** Let `g : V ⟶ B` be smooth of pure
relative dimension `d` with a closed section `s`, and let `N_s ⟶ B` be the normal cone of `s`
with its zero section. Then the deformation datum of
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` exists: étale-locally there are
relative coordinates `x₁, …, x_d` on `V` in which `s` is `x_i = 0`, and on the deformation
chart `u_i = x_i / t` the deformation is `𝔸^d × 𝔸¹` over the base, which gives both the
smoothness of `g̃` and the two cartesian squares.

All of this commutes with base change in `B` and with étale localization.

Since `g` is separated and compactifiable, so is `g̃`: the deformation space is open in the
blow-up of `V̄ ×_B 𝔸¹_B` along `s(B) × {0}`, for a compactification `V̄` of `g`, and this
blow-up is proper over `𝔸¹_B`.

The fibre over `t = 0` is the normal bundle `N_s = Spec_B (Sym (I/I²)) = V(s^* Ω_{V/B})` of the
section (`AlgebraicGeometry.Scheme.Hom.sectionNormalCone`). For an arbitrary normal cone datum in
place of `N_s` the statement would be false: for `B` a smooth projective curve with a nontrivial
line bundle `L`, `V = 𝔸¹_B`, `s` the zero section and the total space of `L`, the line bundle
`s̃^* Ω_{𝒟/𝔸¹_B}` would restrict to `𝒪_B` at `t = 1` and to `L^∨` at `t = 0`, contradicting
`Pic(𝔸¹_B) = Pic(B)`. -/
theorem nonempty_deformationToNormalConeData (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [HasCompactification g] (s : B ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    Nonempty (DeformationToNormalConeData d g s (g.sectionNormalCone s d)) :=
  sorry

end Scheme.Hom

end AlgebraicGeometry
