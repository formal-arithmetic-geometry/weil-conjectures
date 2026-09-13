/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Push- and pullback of ideal sheaves on affine opens

For a morphism `f : X ⟶ Y` of schemes with affine target, the pushforward `I.map f` is on
global sections the preimage ideal along `f.appTop`. Dually, for a morphism of affine
schemes the pullback `J.comap f` is the extended ideal, that is `Ideal.map` along `f.appTop`;
in the relative form used in practice, for affine opens `V ⊆ f ⁻¹ᵁ U` the ideal of `J.comap f`
on `V` is the extension of the ideal of `J` on `U` along `f.appLE U V`.

The affine statement is not proved by computing the fibre product of the two affine schemes
involved: `Scheme.IdealSheafData.comap` is a left adjoint (`Scheme.IdealSheafData.map_gc`)
and on an affine scheme ideal sheaves are order-isomorphic to ideals of the global sections
(`Scheme.IdealSheafData.equivOfIsAffine`). Under these identifications the right adjoint is
`Ideal.comap`, hence the left adjoint is `Ideal.map`.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.ideal_top_map_of_isAffine`
- `AlgebraicGeometry.Scheme.IdealSheafData.ideal_top_comap_of_isAffine`
- `AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE`

A last group records that a vanishing power of an ideal sheaf on an affine scheme is
inherited by its pullback along an arbitrary morphism
(`AlgebraicGeometry.Scheme.IdealSheafData.pow_comap_eq_zero_of_isAffine`); this is how a
square-zero thickening of an affine scheme stays square zero after base change.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The pushforward of an ideal sheaf along a morphism of affine schemes is, on global
sections, the preimage ideal. -/
lemma ideal_top_map_of_isAffine [IsAffine X] [IsAffine Y] (I : X.IdealSheafData) (f : X ⟶ Y) :
    (I.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
  rw [map, ker_of_isAffine]
  simp only [ofIdealTop_ideal, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    CommRingCat.hom_id, Ideal.map_id]
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, ← RingHom.comap_ker,
    ker_subschemeι_app I ⟨⊤, isAffineOpen_top X⟩]

/-- The pullback of an ideal sheaf along a morphism of affine schemes is, on global sections,
the extended ideal. -/
lemma ideal_top_comap_of_isAffine [IsAffine X] [IsAffine Y] (J : Y.IdealSheafData) (f : X ⟶ Y) :
    (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  refine le_antisymm ?_ ?_
  · have h : J.comap f ≤ ofIdealTop ((J.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom) :=
      le_map_iff_comap_le.mp <| le_of_isAffine <| by
        rw [ideal_top_map_of_isAffine]
        simpa using Ideal.le_comap_map
    simpa using h ⟨⊤, isAffineOpen_top X⟩
  · rw [Ideal.map_le_iff_le_comap, ← ideal_top_map_of_isAffine]
    exact le_map_comap J f ⟨⊤, isAffineOpen_top Y⟩

/-- Restricting an ideal sheaf to an affine open subscheme recovers its ideal there. -/
lemma map_topIso_ideal_top_comap_ι (J : X.IdealSheafData) (U : X.affineOpens) :
    haveI : IsAffine U.1.toScheme := U.2
    ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩).map U.1.topIso.hom.hom =
      J.ideal U := by
  have : IsAffine U.1.toScheme := U.2
  rw [ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  rw [Scheme.Opens.topIso_hom]
  exact map_ideal' (I := J)
    (V := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩)
    (U := U) _

/-- **The pullback of an ideal sheaf is the extended ideal.** If `V` is an affine open of `Z`
lying over the affine open `U` of `X`, then the ideal of `J.comap f` on `V` is the ideal of
`J` on `U` extended along `f.appLE U V`. -/
lemma ideal_comap_appLE {Z : Scheme.{u}} (J : X.IdealSheafData) (f : Z ⟶ X)
    (U : X.affineOpens) (V : Z.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (J.comap f).ideal V = (J.ideal U).map (f.appLE U.1 V.1 e).hom := by
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have hres : (J.comap f).comap V.1.ι = (J.comap U.1.ι).comap (f.resLE U.1 V.1 e) := by
    rw [← comap_comp, ← comap_comp, Scheme.Hom.resLE_comp_ι]
  rw [← map_topIso_ideal_top_comap_ι (J.comap f) V, hres,
    ideal_top_comap_of_isAffine, Ideal.map_map, ← map_topIso_ideal_top_comap_ι J U,
    Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ### Powers of an ideal sheaf -/

/-- Over an affine scheme, an ideal sheaf has vanishing `n`-th power as soon as the ideal of
global sections does. -/
lemma pow_eq_zero_of_isAffine [IsAffine X] {I : X.IdealSheafData} {n : ℕ}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n = ⊥) : I ^ n = 0 :=
  ext_of_isAffine (by rw [show (I ^ n).ideal ⟨⊤, isAffineOpen_top X⟩ =
    I.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n from rfl, h]; rfl)

/-- **A power of an ideal sheaf on an affine scheme stays zero after pullback.** If `J` is an
ideal sheaf on an affine scheme `Y` with `J ^ n = 0`, then `(J.comap f) ^ n = 0` for every
morphism `f : X ⟶ Y`. -/
lemma pow_comap_eq_zero_of_isAffine [IsAffine Y] {J : Y.IdealSheafData} {n : ℕ}
    (hJ : J ^ n = 0) (f : X ⟶ Y) : J.comap f ^ n = 0 := by
  refine IdealSheafData.ext (funext fun U ↦ ?_)
  have h : (J.comap f).ideal U =
      (J.ideal ⟨⊤, isAffineOpen_top Y⟩).map (f.appLE ⊤ U.1 le_top).hom :=
    ideal_comap_appLE J f ⟨⊤, isAffineOpen_top Y⟩ U le_top
  have hJ' : J.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n = ⊥ := by
    rw [show J.ideal ⟨⊤, isAffineOpen_top Y⟩ ^ n = (J ^ n).ideal ⟨⊤, isAffineOpen_top Y⟩ from rfl,
      hJ]; rfl
  rw [show (J.comap f ^ n).ideal U = (J.comap f).ideal U ^ n from rfl, h, ← Ideal.map_pow, hJ']
  simp

/-- If the kernel of a ring homomorphism `φ` has vanishing `n`-th power, so does the kernel
ideal sheaf of `Spec φ`. -/
lemma pow_ker_spec_map_eq_zero {R S : CommRingCat.{u}} {n : ℕ} (φ : R ⟶ S)
    (hφ : RingHom.ker φ.hom ^ n = ⊥) :
    (Spec.map φ).ker ^ n = 0 := by
  refine IdealSheafData.pow_eq_zero_of_isAffine ?_
  have hinj : Function.Injective (ΓSpecIso S).inv.hom :=
    ((ConcreteCategory.isIso_iff_bijective (ΓSpecIso S).inv).mp inferInstance).injective
  have he : (Spec.map φ).appTop = (ΓSpecIso R).hom ≫ φ ≫ (ΓSpecIso S).inv := by
    rw [ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hk : RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (ΓSpecIso R).hom.hom := by
    ext x
    simp only [he, CommRingCat.hom_comp, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply,
      Ideal.mem_comap]
    exact ⟨fun hx ↦ hinj (by simpa using hx), fun hx ↦ by simp [hx]⟩
  rw [Hom.ker_apply, show (Spec.map φ).app ⊤ = (Spec.map φ).appTop from rfl, hk]
  refine le_bot_iff.mp ((Ideal.le_comap_pow _ n).trans ?_)
  rw [hφ, ← RingHom.ker_eq_comap_bot]
  exact le_of_eq (RingHom.ker_coe_equiv (ΓSpecIso R).commRingCatIsoToRingEquiv)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A morphism `Spec R ⟶ X` that factors as `Spec ψ` followed by the canonical morphism
`Spec Γ(X, U) ⟶ X` of an affine open `U` induces `ψ` on sections over `U`. -/
lemma appLE_top_specMap_fromSpec {R : CommRingCat.{u}} (U : X.affineOpens)
    (ψ : Γ(X, U.1) ⟶ R) (e : (⊤ : (Spec R).Opens) ≤ (Spec.map ψ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    (Spec.map ψ ≫ U.2.fromSpec).appLE U.1 ⊤ e = ψ ≫ (Scheme.ΓSpecIso R).inv := by
  apply Spec.map_injective
  rw [← cancel_mono U.2.fromSpec,
    IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 (isAffineOpen_top (Spec R)),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp, Category.assoc]

lemma top_le_preimage_specMap_fromSpec {R : CommRingCat.{u}} (U : X.affineOpens)
    (ψ : Γ(X, U.1) ⟶ R) : (⊤ : (Spec R).Opens) ≤ (Spec.map ψ ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
  rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
  simp

namespace Scheme.IdealSheafData

/-- **The extended ideal on an affine chart.** If a morphism `Spec R ⟶ X` factors as `Spec ψ`
followed by the canonical morphism of an affine open `U`, then the pullback of an ideal sheaf
`J` along it is the extension of `J.ideal U` along `ψ`. -/
lemma ideal_top_comap_specMap_fromSpec (J : X.IdealSheafData) (U : X.affineOpens)
    {R : CommRingCat.{u}} (ψ : Γ(X, U.1) ⟶ R) :
    (J.comap (Spec.map ψ ≫ U.2.fromSpec)).ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ =
      ((J.ideal U).map ψ.hom).map (Scheme.ΓSpecIso R).inv.hom := by
  rw [ideal_comap_appLE J _ U ⟨⊤, isAffineOpen_top (Spec R)⟩
      (top_le_preimage_specMap_fromSpec U ψ),
    appLE_top_specMap_fromSpec, CommRingCat.hom_comp, ← Ideal.map_map]

/-- The unbundled form of `ideal_top_comap_specMap_fromSpec`. -/
lemma ideal_top_comap_specMap_ofHom_fromSpec (J : X.IdealSheafData) (U : X.affineOpens)
    {R : Type u} [CommRing R] (ψ : Γ(X, U.1) →+* R) :
    (J.comap (Spec.map (CommRingCat.ofHom ψ) ≫ U.2.fromSpec)).ideal
        ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      ((J.ideal U).map ψ).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  ideal_top_comap_specMap_fromSpec J U (CommRingCat.ofHom ψ)

end Scheme.IdealSheafData

end AlgebraicGeometry

