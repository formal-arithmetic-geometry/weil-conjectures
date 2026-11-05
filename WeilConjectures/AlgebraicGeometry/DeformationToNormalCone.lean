/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Compactification.NagataCompactification

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

The deformation space is constructed as the relative spectrum `D_s V = Spec_V 𝒪_V[t, I t⁻¹]`
of the extended Rees algebra of the ideal `I` of `s(B)`
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`), and the normal cone `N_s` as the
relative spectrum of `𝒪_V[t, I t⁻¹] / t = ⨁_{r ≥ 0} I^r / I^{r+1}`, which lies over `s(B) ≅ B`
(`AlgebraicGeometry.Scheme.Hom.normalConeData`). The fibre squares come from pushout squares of
quasi-coherent algebras. Smoothness of `g̃` is proved on charts: near `s(B)` there are étale
coordinates in which `s` is the origin, and there the deformation space is étale over
`𝔸^d × 𝔸¹` (`AlgebraicGeometry.exists_smoothOfRelativeDimension_extendedReesAlgebra_of_section`).

The structure `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` records the clauses of
`sk-lem-geometry` about the deformation; the blueprint lemma is the statement that such a datum
exists with the normal cone of `s` as fibre over `t = 0`. The punctured trivialisation `κ°` of
`sk-lem-geometry` (3) — the identification of the deformation over `𝔾_{m,B}` with
`V ×_B 𝔾_{m,B}` — is a field. `𝔾_m` is not a Mathlib scheme, so `𝔾_{m,B}` is carried as an open
subscheme of `𝔸¹_B` whose underlying set is the complement of the zero section, as in
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.normalConeData`: the normal cone of a closed section.
- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`: the deformation space `𝒟_s V`
  together with `g̃`, `s̃` and the properties characterising them.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj`
- `AlgebraicGeometry.Scheme.Hom.normalConeData`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

/-! ### The construction -/

section Construction

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-! #### The fibre over `t = 0` -/

/-! #### The punctured trivialisation -/

/-! #### The fibre over `t = 1` -/

end Construction

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

The fibre over `t = 0` is the normal cone datum `N`.

In the purity conventions every scheme is separated of finite type over the base field, so
`g̃` and the coordinate chart are moreover separated and compactifiable, and every open
immersion is quasi-compact; this is recorded, compactifiability being what makes the dualizing
complexes defined.

Existence of the datum with `N` the normal cone of `s`
(`AlgebraicGeometry.Scheme.Hom.normalConeData`) is
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

section Charts

open _root_.Polynomial

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-- The standard smooth charts of `g` can be shrunk around a point of the source to basic
opens. -/
lemma exists_isStandardSmooth_appLE_basicOpen (d : ℕ) [SmoothOfRelativeDimension d g] (v : V)
    (O : V.Opens) (hvO : v ∈ O) :
    ∃ (W : B.Opens) (_ : IsAffineOpen W) (U : V.Opens) (_ : IsAffineOpen U) (_ : v ∈ U)
      (_ : U ≤ O) (hUW : U ≤ g ⁻¹ᵁ W),
      (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨W, hW, U₀, hU₀, hvU₀, e, hQ⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := g) v
  obtain ⟨r, hrO, hvr⟩ := hU₀.exists_basicOpen_le (V := O) ⟨v, hvO⟩ hvU₀
  refine ⟨W, hW, V.basicOpen r, hU₀.basicOpen r, hvr, hrO, (V.basicOpen_le r).trans e, ?_⟩
  have := hU₀.isLocalization_basicOpen r
  have h := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
    d).right Γ(V, V.basicOpen r) r _ hQ
  rwa [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at h

lemma basicOpen_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {W : Y'.Opens} {U : X'.Opens}
    (e : U ≤ f ⁻¹ᵁ W) (r : Γ(Y', W)) :
    X'.basicOpen (f.appLE W U e r) = U ⊓ f ⁻¹ᵁ Y'.basicOpen r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, Scheme.preimage_basicOpen]

/-- **Étale coordinates along the section.** Near a point `s(b)` there are an affine open
`W ∋ b` of `B` and an affine open `U ⊆ g⁻¹ W` of `V` with `s⁻¹ U = W`, together with étale
coordinates `ψ : Γ(W)[X₁, …, X_d] ⟶ Γ(U)` over `Γ(W)` generating the ideal of the section. -/
lemma exists_etale_coordinates_of_mem_range (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) (b : B) :
    ∃ (W : B.Opens) (_ : IsAffineOpen W) (U : V.AffineZariskiSite) (hUW : U.1 ≤ g ⁻¹ᵁ W),
      b ∈ W ∧ s ⁻¹ᵁ U.1 = W ∧ ∃ ψ : MvPolynomial (Fin d) Γ(B, W) →+* Γ(V, U.1), ψ.Etale ∧
        ψ.comp MvPolynomial.C = (g.appLE W U.1 hUW).hom ∧
        s.ker.siteIdeal U = (Ideal.mvPolynomialOrigin Γ(B, W) (Fin d)).map ψ := by
  have hgs : ∀ b, g (s b) = b := fun b ↦ by rw [← Scheme.Hom.comp_apply, hs]; rfl
  obtain ⟨W₀, hW₀, U₀, hU₀, hvU₀, -, hUW₀, hQ₀⟩ :=
    exists_isStandardSmooth_appLE_basicOpen g d (s b) ⊤ trivial
  have hbW₀ : b ∈ W₀ := hgs b ▸ hUW₀ hvU₀
  obtain ⟨c, hcU, hbc⟩ := hW₀.exists_basicOpen_le (V := s ⁻¹ᵁ U₀) ⟨b, hvU₀⟩ hbW₀
  set W := B.basicOpen c
  have hW : IsAffineOpen W := hW₀.basicOpen c
  set U := V.basicOpen (g.appLE W₀ U₀ hUW₀ c)
  have hU : IsAffineOpen U := hU₀.basicOpen _
  have hUW : U ≤ g ⁻¹ᵁ W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c]; exact inf_le_right
  have hsU : s ⁻¹ᵁ U = W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c, Scheme.Hom.preimage_inf,
      ← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
    exact inf_eq_right.mpr hcU
  have hQ : (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
    have := hW₀.isLocalization_basicOpen c
    have := hU₀.isLocalization_basicOpen (g.appLE W₀ U₀ hUW₀ c)
    have := hW₀.appLE_eq_away_map g hU₀ hUW₀ c
    rw [this]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away _ _ _ _ hQ₀
  -- the section as a retraction of rings
  let f := g.appLE W U hUW
  let σ := s.appLE U W hsU.ge
  have hσf : σ.hom.comp f.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appLE_congr_hom hs _ _ _ (by simp)]
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    erw [B.presheaf.map_id]
    rfl
  obtain ⟨φ, hφf, hφ⟩ := hQ.exists_etale_mvPolynomial
  obtain ⟨a, hσa, H⟩ := exists_etale_coordinates_of_section f.hom σ.hom hσf φ hφ hφf
  have hσ : σ = s.app U ≫ B.presheaf.map (eqToHom hsU.symm).op := rfl
  have hinj : Function.Injective (B.presheaf.map (eqToHom hsU.symm).op).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  set U' := V.basicOpen a
  have hU' : IsAffineOpen U' := hU.basicOpen a
  have hU'W : U' ≤ g ⁻¹ᵁ W := (V.basicOpen_le a).trans hUW
  have := hU.isLocalization_basicOpen a
  obtain ⟨ψ, hψ, hψf, hJ⟩ := H Γ(V, U')
  refine ⟨W, hW, ⟨U', hU'⟩, hU'W, hbc, ?_, ψ, hψ, ?_, ?_⟩
  · have hb : B.basicOpen (σ a) = W := by
      rw [hσa, Scheme.basicOpen_of_isUnit _ isUnit_one]
    rw [hσ, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hb
    refine le_antisymm ((s.preimage_mono (V.basicOpen_le a)).trans hsU.le) ?_
    exact hb.ge.trans inf_le_right
  · rw [hψf, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  · rw [← hJ, hσ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
      ← Scheme.Hom.ker_apply s ⟨U, hU⟩]
    exact (s.ker.map_ideal_basicOpen ⟨U, hU⟩ a).symm

end Charts

section Smooth

open AffineZariskiSite

variable (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s]

variable {g s}

end Smooth

section Separated

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

end Separated

end Scheme.Hom

end AlgebraicGeometry
