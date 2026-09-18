/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Complements on pullback and pushforward of ideal sheaves

Four groups of complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.

The first computes the pullback of an ideal sheaf along the inclusion of its own closed
subscheme, which vanishes; as a consequence a morphism is scheme-theoretically dense in
its own scheme-theoretic image.

The second describes the pullback of an ideal sheaf along an open immersion on affine
opens, where it is the transport of the ideal of sections along the isomorphism of section
rings, and gives the resulting comparison criteria.

The third is flat base change: for a quasi-compact `g` and a cartesian square with flat
right-hand edge, pushforward along `g` commutes with pullback along the base change. This
is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap` language.

The fourth computes push- and pullback on affine opens, and deduces from this local
description that pullback commutes with products. For a morphism `f : X ⟶ Y` of schemes
with affine target, the pushforward `I.map f` is on global sections the preimage ideal along
`f.appTop`; dually, for a morphism of affine schemes the pullback `J.comap f` is the extended
ideal, that is `Ideal.map` along `f.appTop`. The affine statement is not proved by computing
the fibre product of the two affine schemes involved: `Scheme.IdealSheafData.comap` is a left
adjoint (`Scheme.IdealSheafData.map_gc`) and on an affine scheme ideal sheaves are
order-isomorphic to ideals of the global sections (`Scheme.IdealSheafData.equivOfIsAffine`).
Under these identifications the right adjoint is `Ideal.comap`, hence the left adjoint is
`Ideal.map`.

The fourth also computes the stalks of a pullback: the stalk of `J.comap f` at a point `v` is
the extension of the stalk of `J` at `f v` along the stalk map of `f`
(`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_comap`). Both sides are computed on an
affine open of the source lying over an affine open of the target, where the statement is again
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE`.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_comap`: the set-level form of
  `support_comap`, `(I.comap f).support = f ⁻¹' I.support` as sets;
- `AlgebraicGeometry.Scheme.Hom.comap_ker_self`: `j.ker.comap j = ⊥` for every `j`;
- `AlgebraicGeometry.Scheme.IdealSheafData.fg_ideal_comap_iff`: finite generation of the
  ideal of sections transfers across an open immersion;
- `AlgebraicGeometry.Scheme.IdealSheafData.subschemeMapOfComapLe`: the morphism of closed
  subschemes `V(J) ⟶ V(I)` induced by a morphism `f` with `I.comap f ≤ J`;
- `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback`: flat base change, with
  `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_opens` (restriction to an open) and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_map` (a quasi-compact flat monomorphism)
  as special cases;
- `AlgebraicGeometry.Scheme.IdealSheafData.ideal_top_map_of_isAffine` and
  `AlgebraicGeometry.Scheme.IdealSheafData.ideal_top_comap_of_isAffine`: push- and pullback on
  global sections of affine schemes, with
  `AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE` the relative form used in
  practice and `AlgebraicGeometry.Scheme.IdealSheafData.ideal_top_comap_specMap_fromSpec` the
  form on an affine chart;
- `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_comap`: the stalk of a pullback of ideal
  sheaves is the extension of the stalk along the stalk map;
- `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul` and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_pow`: pullback of ideal sheaves commutes with
  products and powers.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

section Support

/-- The underlying set of the support of the pullback of an ideal sheaf is the preimage
of the underlying set of its support: the set-level form of
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`. -/
lemma coe_support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    ((I.comap f).support : Set X) = f ⁻¹' (I.support : Set Y) := by
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage]

end Support

section Subscheme

/-- An ideal sheaf pulls back to zero along the inclusion of the closed subscheme it cuts
out: the inclusion is a monomorphism, so it is its own kernel pair. -/
lemma comap_subschemeι (I : X.IdealSheafData) : I.comap I.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst I.subschemeι I.subschemeι)

/-- Every morphism is scheme-theoretically dense in its scheme-theoretic image: the ideal
sheaf cutting the image out pulls back to zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.comap_ker_self (j : X ⟶ Y) : j.ker.comap j = ⊥ := by
  have hfac : j.ker.comap j = (j.ker.comap j.imageι).comap j.toImage := by
    rw [← comap_comp, j.toImage_imageι]
  rw [hfac, comap_subschemeι, comap_bot]

end Subscheme

section OpenImmersion

variable {Z T : Scheme.{u}} (j : Z ⟶ T) [IsOpenImmersion j] (I : T.IdealSheafData)

/-- Pullback of ideal sheaves along an open immersion commutes with intersections. -/
lemma comap_inf_of_isOpenImmersion (K : T.IdealSheafData) :
    (I ⊓ K).comap j = I.comap j ⊓ K.comap j := by
  ext U : 2
  simp only [ideal_inf, Pi.inf_apply, ideal_comap_of_isOpenImmersion, Ideal.comap_inf]

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion is the
transport of the ideal of sections on the image along the isomorphism of section rings. -/
lemma ideal_comap_eq_map_appIso (U : Z.affineOpens) :
    (I.comap j).ideal U =
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).map (j.appIso U.1).hom.hom := by
  rw [ideal_comap_of_isOpenImmersion, CommRingCat.comap_inv_eq_map]

/-- Finite generation of the ideal of sections is detected on either side of an open
immersion. -/
lemma fg_ideal_comap_iff (U : Z.affineOpens) :
    ((I.comap j).ideal U).FG ↔
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).FG := by
  rw [ideal_comap_eq_map_appIso]
  refine ⟨fun h ↦ ?_, fun h ↦ h.map _⟩
  have h' := h.map (j.appIso U.1).inv.hom
  rwa [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id] at h'

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion,
computed on an affine open of the source lying over an affine open `V` of the target: it
is the extension of the ideal of sections on `V` along the restriction map `appLE`. -/
lemma ideal_comap_eq_map_appLE (V : T.affineOpens) (U : Z.affineOpens)
    (h : U.1 ≤ j ⁻¹ᵁ V.1) :
    (I.comap j).ideal U = (I.ideal V).map (j.appLE V.1 U.1 h).hom := by
  have himg : (⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ : T.affineOpens) ≤ V :=
    Subtype.coe_le_coe.mp <| (j.image_mono h).trans <| by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right
  rw [ideal_comap_eq_map_appIso, ← map_ideal I himg, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- To compare two pullbacks of ideal sheaves along an open immersion, it suffices to
compare the ideals of sections on a family of affine opens contained in the range whose
preimages cover the source. -/
lemma comap_le_comap_of_ideal_le {I K : T.IdealSheafData} {ι : Type*} (U : ι → T.affineOpens)
    (hran : ∀ i, (U i).1 ≤ j.opensRange) (hcov : j.opensRange ≤ ⨆ i, (U i).1)
    (H : ∀ i, I.ideal (U i) ≤ K.ideal (U i)) :
    I.comap j ≤ K.comap j := by
  refine le_of_iSup_eq_top
    (fun i ↦ ⟨j ⁻¹ᵁ (U i).1, (U i).2.preimage_of_isOpenImmersion j (hran i)⟩) ?_ fun i ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ⟨x, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion]
    refine Ideal.comap_mono ?_
    have himg : j ''ᵁ (j ⁻¹ᵁ (U i).1) = (U i).1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hran i)]
    have hcongr : (⟨j ''ᵁ (j ⁻¹ᵁ (U i).1),
        ((U i).2.preimage_of_isOpenImmersion j (hran i)).image_of_isOpenImmersion j⟩ :
        T.affineOpens) = U i := Subtype.ext himg
    have hle := H i
    rw [← hcongr] at hle
    exact hle

end OpenImmersion

section FlatBaseChange

/-- Flat base change for pushforward of ideal sheaves: for a cartesian square whose
right-hand edge `q` is flat and whose left-hand edge `g` is quasi-compact, pushing forward
along `g` and then restricting along `q` is restricting along `p` and then pushing forward
along `g'`. This is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap`
language (Stacks Project Tag 081I). -/
theorem map_comap_of_isPullback {X' Y' : Scheme.{u}} (B : Y.IdealSheafData) {g : Y ⟶ X}
    [QuasiCompact g] {q : X' ⟶ X} [Flat q] {g' : Y' ⟶ X'} {p : Y' ⟶ Y}
    (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have hker : ∀ {Z W : Scheme.{u}} (C : Z.IdealSheafData) (φ : Z ⟶ W),
      C.map φ = (C.subschemeι ≫ φ).ker := fun C φ ↦ by
    rw [Scheme.Hom.ker_comp, ker_subschemeι]
  -- paste the defining square of `B.comap p` onto the given cartesian square
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip).flip
  have hsub : (B.comap p).subschemeι = (B.comapIso p).hom ≫ pullback.fst p B.subschemeι :=
    (comapIso_hom_fst _ _).symm
  rw [hker B g, hker (B.comap p) g', ← Scheme.Hom.ker_pullback_snd (B.subschemeι ≫ g) q,
    hsub, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- Restriction of a pushforward to an open subscheme, the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the open immersion
`O.ι`, which is flat. -/
theorem map_comap_opens (g : Y ⟶ X) [QuasiCompact g] (B : Y.IdealSheafData) (O : X.Opens) :
    (B.map g).comap O.ι = (B.comap (g ⁻¹ᵁ O).ι).map (g ∣_ O) :=
  map_comap_of_isPullback B (isPullback_morphismRestrict g O).flip

/-- The pushforward of an ideal sheaf along a quasi-compact flat monomorphism — for
instance the inclusion of a quasi-compact open — restricts back to the original ideal
sheaf. This is the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the kernel pair of a
monomorphism. -/
theorem comap_map (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Mono f] (J : X.IdealSheafData) :
    (J.map f).comap f = J := by
  rw [map_comap_of_isPullback J (IsKernelPair.id_of_mono f), comap_id, map_id]

end FlatBaseChange

section Subscheme

/-- The morphism `V(J) ⟶ V(I)` of closed subschemes induced by a morphism `f : X ⟶ Y` that
pulls the ideal `I` into the ideal `J`. It is
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeMap` fed through the Galois connection
`AlgebraicGeometry.Scheme.IdealSheafData.le_map_iff_comap_le`. -/
noncomputable def subschemeMapOfComapLe {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (J : X.IdealSheafData) (f : X ⟶ Y) (hf : I.comap f ≤ J) : J.subscheme ⟶ I.subscheme :=
  subschemeMap J I f (le_map_iff_comap_le.mpr hf)

/-- The morphism of closed subschemes lies over `f`:

```
  V(J) ──subschemeMapOfComapLe──▶ V(I)
    │                               │
    │ J.subschemeι                  │ I.subschemeι
    ▼                               ▼
    X ────────────f───────────────▶ Y
```
-/
@[reassoc (attr := simp)]
lemma subschemeMapOfComapLe_subschemeι {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (J : X.IdealSheafData) (f : X ⟶ Y) (hf : I.comap f ≤ J) :
    subschemeMapOfComapLe I J f hf ≫ I.subschemeι = J.subschemeι ≫ f :=
  subschemeMap_subschemeι _ _ _ _

end Subscheme

section AffineOpens

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

/-- **The stalk of a pullback of ideal sheaves is the extension of the stalk.** For a morphism
`p : X ⟶ Y`, an ideal sheaf `I` on `Y` and a point `v` of `X`, the stalk of `I.comap p` at `v`
is the ideal of `𝒪_{X, v}` generated by the image of the stalk of `I` at `p v` under the stalk
map of `p`.

Both sides are computed on an affine open `V` of `X` lying over an affine open `U` of `Y` by
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ`, where the statement becomes
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE`. No hypothesis on `p` or `I` is
needed: an ideal sheaf is quasi-coherent by construction, so `(I.comap p)(V)` really is the
extended ideal `I(U)·Γ(X, V)` and not merely something containing it. -/
lemma stalkIdeal_comap {X Y : Scheme.{u}} (I : Y.IdealSheafData) (p : X ⟶ Y) (v : X) :
    (I.comap p).stalkIdeal v = (I.stalkIdeal (p.base v)).map (p.stalkMap v).hom := by
  obtain ⟨U, V, hVU, hv⟩ := exists_affineOpens_le_preimage p v
  rw [stalkIdeal_eq_map_germ _ v V hv, stalkIdeal_eq_map_germ _ (p.base v) U (hVU hv),
    ideal_comap_appLE I p U V hVU, Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res]
  exact (p.germ_stalkMap U.1 v (hVU hv)).symm

end AffineOpens

section Products

/-- **Inverse images of ideal sheaves commute with products.** Both sides are computed on an
affine open `W` of `X` lying over an affine open `V` of `Y` by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_appLE`, where the statement becomes
multiplicativity of `Ideal.map`; such pairs `W ≤ f ⁻¹ᵁ V` cover `X`. -/
theorem comap_mul (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine ext_of_iSup_eq_top
    (ι := {p : Y.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1}) (fun p ↦ p.1.2) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨V, W, hle, hxW⟩ := exists_affineOpens_le_preimage f x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(V, W), hle⟩, hxW⟩
  · rintro ⟨⟨V, W⟩, hle⟩
    rw [ideal_comap_appLE (I * J) f V W hle, ideal_mul, Pi.mul_apply, Ideal.map_mul,
      ideal_mul, Pi.mul_apply, ideal_comap_appLE I f V W hle, ideal_comap_appLE J f V W hle]

/-- **Inverse images of ideal sheaves commute with powers.** -/
theorem comap_pow (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => simp [comap_top]
  | succ n ih => rw [pow_succ, comap_mul, ih, ← pow_succ]

end Products

end AlgebraicGeometry.Scheme.IdealSheafData
