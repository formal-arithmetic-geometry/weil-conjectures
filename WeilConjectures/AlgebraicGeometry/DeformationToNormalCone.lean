/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

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
space, the two structure morphisms and the four clauses of `sk-lem-geometry`, and the
blueprint lemma is the statement that such a datum exists.

The punctured trivialisation `κ°` of `sk-lem-geometry` (3) — the identification of the
deformation over `𝔾_{m,B}` with `V ×_B 𝔾_{m,B}` — is a field. `𝔾_m` is not a Mathlib scheme,
so `𝔾_{m,B}` is carried as an open subscheme of `𝔸¹_B` whose underlying set is the complement of
the zero section, as in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

TODO: nothing ties the normal cone datum `N` to the section `s`: the structure
`AlgebraicGeometry.Scheme.Hom.NormalConeData` is not yet the normal cone of `s` (see its TODO), so
the fibre over `t = 0` is only some vector bundle with a zero section. Tying `NormalConeData` to
the conormal sheaf of the immersion is the subject of the smooth-purity follow-up (branch
`prove2/sk-thm-smooth-purity-2`); once it lands, `N` in `DeformationToNormalConeData d g s N`
becomes the normal cone of `s` and no field needs to be added here.

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

/-! ### The construction -/

section Construction

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-- The projection `g̃ : D_s V ⟶ 𝔸¹_B` of the deformation space of the section `s`, given by the
coordinate `t` and `D_s V ⟶ V ⟶ B`. -/
noncomputable def deformationSpaceProj : s.ker.deformationSpace ⟶ 𝔸(ULift.{u} (Fin 1); B) :=
  s.ker.deformationSpaceToPolynomialSpec ≫ V.polynomialSpecToAffineSpace ≫
    AffineSpace.map (ULift.{u} (Fin 1)) g

/-- `B` is the closed subscheme `V(I_s) = Spec_V (𝒪_V / I_s)`. -/
noncomputable def toQuotientSpec : B ⟶ s.ker.quotientSpec :=
  IsClosedImmersion.lift (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase s
    (s.ker.ker_quotientSpec_toBase).le

@[reassoc (attr := simp)]

lemma toQuotientSpec_toBase :
    s.toQuotientSpec ≫ (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase = s :=
  IsClosedImmersion.lift_fac _ _ _

instance [IsClosedImmersion s] : IsIso s.toQuotientSpec :=
  IsClosedImmersion.isIso_of_ker_eq _ _ _ (s.toQuotientSpec_toBase)
    (s.ker.ker_quotientSpec_toBase).symm

/-- The projection `N_s ⟶ B` of the normal cone of the section. -/
noncomputable def normalConeProj : s.ker.normalCone ⟶ B :=
  (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase ≫ g

/-- The zero section `B ⟶ N_s` of the normal cone, given by the degree-zero part
`⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_V / I`. -/
noncomputable def normalConeZeroSection : B ⟶ s.ker.normalCone :=
  s.toQuotientSpec ≫ relativeGluingMap s.ker.coequifibered_toNormalConePresheaf
    s.ker.coequifibered_toQuotientAlgebra s.ker.normalConeToQuotient


@[reassoc (attr := simp)]
lemma normalConeZeroSection_toBase :
    s.normalConeZeroSection ≫ (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase =
      s := by
  rw [normalConeZeroSection, Category.assoc,
    relativeGluingMap_toBase _ _ _ s.ker.toNormalConePresheaf_comp_normalConeToQuotient,
    toQuotientSpec_toBase]

variable {g s} in
lemma normalConeZeroSection_normalConeProj (hs : s ≫ g = 𝟙 B) :
    s.normalConeZeroSection ≫ normalConeProj g s = 𝟙 B := by
  rw [normalConeProj, normalConeZeroSection_toBase_assoc, hs]

instance [IsClosedImmersion s] : IsClosedImmersion s.normalConeZeroSection := by
  have : IsClosedImmersion (s.normalConeZeroSection ≫
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase) := by
    rw [normalConeZeroSection_toBase]; infer_instance
  exact IsClosedImmersion.of_comp _
    (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase

/-- `𝔸¹_B ⟶ 𝔸¹_{V(I_s)} = Spec_V (𝒪_V / I_s)[t]`, the affine line over `B ≅ V(I_s)`. -/
noncomputable def affineSpaceToQuotientPolynomialSpec :
    𝔸(ULift.{u} (Fin 1); B) ⟶ s.ker.quotientPolynomialSpec :=
  s.ker.isPullback_quotientPolynomialSpec.lift
    ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s.toQuotientSpec)
    (AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace) (by
      rw [Category.assoc, toQuotientSpec_toBase, Category.assoc,
        ← polynomialSpecToAffineSpace_over, IsIso.inv_hom_id_assoc, AffineSpace.map_over])

@[reassoc (attr := simp)]
lemma affineSpaceToQuotientPolynomialSpec_toQuotientSpec :
    s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap
      s.ker.coequifibered_toQuotientAlgebra s.ker.coequifibered_toQuotientPolynomialAlgebra
      (s.ker.quotientAlgebra.whiskerLeft CommRingCat.polynomialC) =
      (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s.toQuotientSpec :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma affineSpaceToQuotientPolynomialSpec_toPolynomialSpec :
    s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap
      V.coequifibered_toPolynomialPresheaf s.ker.coequifibered_toQuotientPolynomialAlgebra
      s.ker.polynomialToQuotientPolynomial =
      AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace :=
  IsPullback.lift_snd _ _ _ _

/-- The section `s̃ : 𝔸¹_B ⟶ D_s V` of `g̃`: on the extended Rees algebra it is
`𝒪_V[t, I t⁻¹] ⟶ (𝒪_V / I)[t]`, `t ↦ t`, `x t⁻¹ ↦ 0`. -/
noncomputable def deformationSpaceSection : 𝔸(ULift.{u} (Fin 1); B) ⟶ s.ker.deformationSpace :=
  s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap s.ker.coequifibered_toReesPresheaf
    s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.reesToQuotientPolynomial

lemma toReesPresheaf_comp_reesToQuotientPolynomial :
    s.ker.toReesPresheaf ≫ s.ker.reesToQuotientPolynomial = s.ker.toQuotientPolynomialAlgebra := by
  ext U x
  exact Ideal.extendedReesAlgebraToPolynomial_algebraMap (I := s.ker.siteIdeal U.unop) _
    Ideal.mk_ker.ge x

@[reassoc (attr := simp)]
lemma deformationSpaceSection_toPolynomialSpec :
    s.deformationSpaceSection ≫ s.ker.deformationSpaceToPolynomialSpec =
      AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace := by
  rw [deformationSpaceSection, IdealSheafData.deformationSpaceToPolynomialSpec, Category.assoc,
    ← relativeGluingMap_comp, s.ker.polynomialToRees_comp_reesToQuotientPolynomial,
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec]

@[reassoc (attr := simp)]
lemma deformationSpaceSection_toBase :
    s.deformationSpaceSection ≫ s.ker.deformationSpaceProj =
      (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s := by
  change _ ≫ (relativeGluingData s.ker.coequifibered_toReesPresheaf).toBase = _
  rw [← relativeGluingMap_toBase V.coequifibered_toPolynomialPresheaf
    s.ker.coequifibered_toReesPresheaf s.ker.polynomialToRees
    s.ker.toPolynomialPresheaf_comp_polynomialToRees,
    ← IdealSheafData.deformationSpaceToPolynomialSpec,
    deformationSpaceSection_toPolynomialSpec_assoc,
    show (relativeGluingData V.coequifibered_toPolynomialPresheaf).toBase =
      V.polynomialSpecToAffineSpace ≫ _ from V.polynomialSpecToAffineSpace_over.symm,
    IsIso.inv_hom_id_assoc, AffineSpace.map_over]

variable {g s} in
lemma deformationSpaceSection_deformationSpaceProj (hs : s ≫ g = 𝟙 B) :
    s.deformationSpaceSection ≫ deformationSpaceProj g s = 𝟙 _ := by
  rw [deformationSpaceProj, deformationSpaceSection_toPolynomialSpec_assoc,
    IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp, hs, AffineSpace.map_id]

/-! #### The fibre over `t = 0` -/

/-- `Spec_V 𝒪_V[t] = V ×_B 𝔸¹_B`. -/
lemma isPullback_polynomialSpecProj :
    IsPullback V.polynomialSpecProj (V.polynomialSpecToAffineSpace ≫
      AffineSpace.map (ULift.{u} (Fin 1)) g) g (𝔸(ULift.{u} (Fin 1); B) ↘ B) := by
  refine (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).flip.of_iso
    (asIso V.polynomialSpecToAffineSpace).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp,
      polynomialSpecToAffineSpace_over]
  · simp

/-- The zero section of `Spec_V 𝒪_V[t]` is the base change of the zero section of `𝔸¹_B`. -/
lemma isPullback_polynomialSpecZeroSection :
    IsPullback V.polynomialSpecZeroSection g
      (V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_polynomialSpecProj g)
  · rw [polynomialSpecZeroSection, Category.assoc, ← polynomialSpecToAffineSpace_over,
      ← Category.assoc V.polynomialZeroSpecToPolynomialSpec,
      polynomialZeroSpecToPolynomialSpec_comp_polynomialSpecToAffineSpace, Category.assoc,
      AffineSpace.zeroSection_over, Category.comp_id, IsIso.inv_hom_id,
      AffineSpace.zeroSection_over]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [← Category.assoc, polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace,
      AffineSpace.zeroSection_comp_map]

/-- **The fibre over `t = 0` is the normal cone.** -/
lemma isPullback_normalConeToDeformationSpace :
    IsPullback s.ker.normalConeToDeformationSpace (normalConeProj g s) (deformationSpaceProj g s)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) := by
  have h : IsPullback s.ker.normalConeToDeformationSpace
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase
      s.ker.deformationSpaceToPolynomialSpec V.polynomialSpecZeroSection :=
    s.ker.isPullback_normalConeToDeformationSpace.of_iso (Iso.refl _) (Iso.refl _)
      (asIso (relativeGluingData V.coequifibered_toPolynomialZeroPresheaf).toBase) (Iso.refl _)
      (by simp) (by
        simp only [asIso_hom, Iso.refl_hom, Category.id_comp,
          IdealSheafData.normalConeToPolynomialZeroSpec]
        exact relativeGluingMap_toBase _ _ _
          s.ker.toPolynomialZeroPresheaf_comp_polynomialZeroToNormalCone)
      (by simp) (by simp [polynomialSpecZeroSection])
  exact h.paste_vert (isPullback_polynomialSpecZeroSection g)

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

identifying `g̃⁻¹(𝔾_{m,B})` with `V ×_B 𝔾_{m,B}` over `𝔾_{m,B}`.

The normal cone datum `N` is not yet tied to `s`; see the TODO in the module documentation.

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

attribute [instance] DeformationToNormalConeData.smoothOfRelativeDimension_proj

/-- Blueprint `sk-lem-geometry`: Geometry of the deformation of a section

**Existence of the deformation to the normal cone.** Let `g : V ⟶ B` be smooth of pure
relative dimension `d` with a closed section `s`, and let `N_s ⟶ B` be the normal cone of `s`
with its zero section. Then the deformation datum of
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` exists: étale-locally there are
relative coordinates `x₁, …, x_d` on `V` in which `s` is `x_i = 0`, and on the deformation
chart `u_i = x_i / t` the deformation is `𝔸^d × 𝔸¹` over the base, which gives both the
smoothness of `g̃` and the two cartesian squares.

All of this commutes with base change in `B` and with étale localization.

As long as `AlgebraicGeometry.Scheme.Hom.NormalConeData` is not tied to `s` (see the TODO in the
module documentation), this statement, which quantifies over every datum `N`, is false. Let `B`
be a smooth projective curve with a nontrivial line bundle `L`, `V = 𝔸¹_B`, `s` the zero section,
`d = 1`, and `N` the total space of `L` with its zero section. For a datum `𝒟`, the line bundle
`s̃^* Ω_{𝒟/𝔸¹_B}` on `𝔸¹_B` restricts to `s^* Ω_{V/B} ≅ 𝒪_B` at `t = 1` and to `L^∨` at `t = 0`,
contradicting `Pic(𝔸¹_B) = Pic(B)`. It becomes the blueprint lemma once `N` is the normal cone of
`s`. -/
theorem nonempty_deformationToNormalConeData (d : ℕ) (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    (N : NormalConeData d s) :
    Nonempty (DeformationToNormalConeData d g s N) :=
  sorry

end Scheme.Hom

end AlgebraicGeometry
