/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Complements on the subscheme cut out by an ideal sheaf

This file adds three independent complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

## The ideal cut out on an arbitrary open subset

`Scheme.IdealSheafData` records an ideal `I(U) ≤ Γ(X, U)` for **affine** opens `U` only. The
closed subscheme it cuts out is defined for all of them at once, so the kernel of the
restriction `Γ(X, U) ⟶ Γ(V(I), ι ⁻¹ᵁ U)` extends `I.ideal` to an arbitrary open subset
(`AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens`). The extension is determined by the
affine opens contained in `U` (`mem_idealOfOpens_iff_forall_affineOpens`), which is what turns
statements about `I.ideal` into statements about sections over arbitrary opens: the product of
two ideal sheaves, recorded on affine opens only, still multiplies sections over any open
(`mul_mem_mul_idealOfOpens`), and the kernel ideal sheaf of a quasi-compact morphism consists
of the sections killed by it (`AlgebraicGeometry.Scheme.Hom.mem_idealOfOpens_ker_iff`).

## Base change of the subscheme cut out by an ideal sheaf

The affine cover of the closed subscheme `V(I)` cut out by a quasi-coherent ideal `I` is
obtained by base change: over an affine open `U` of `X`, the square formed by the chart
`Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` of `I.subschemeCover`, the closed immersion `I.subschemeι`
and `U.2.fromSpec` is a pullback
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`).

Pasting this square with `Spec` of the pushout square `CommRingCat.isPushout_quotient`
computes the base change of `I.subschemeι` along an arbitrary affine probe
`Spec.map φ ≫ U.2.fromSpec`: it is the closed immersion cut out by the extended ideal
`I(U)·S` (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`).

## The map to the scheme-theoretic image is scheme-theoretically dominant

For a quasi-compact `f : X ⟶ Y`, Mathlib factors `f` as `f.toImage ≫ f.imageι` through the
scheme-theoretic image, and knows that `f.toImage` is dominant and quasi-compact. It does not
record that `f.toImage` is *scheme-theoretically* dominant, which is the stronger statement
that makes the image the smallest closed subscheme through which `f` factors. This file adds
it, in the form `AlgebraicGeometry.Scheme.Hom.ker_toImage : f.toImage.ker = ⊥`.

The proof is the expected one and uses no new input: `f.toImage.app` is injective over the
preimage of an affine open of `Y` (`AlgebraicGeometry.Scheme.Hom.toImage_app_injective`), those
preimages are affine because `f.imageι` is a closed immersion, and they cover the image, so
the kernel ideal vanishes on a cover by affine opens.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.mem_idealOfOpens_iff_forall_affineOpens`
- `AlgebraicGeometry.Scheme.IdealSheafData.mul_mem_mul_idealOfOpens`
- `AlgebraicGeometry.Scheme.Hom.mem_idealOfOpens_ker_iff`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`
- `AlgebraicGeometry.Scheme.Hom.ker_toImage`
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-! ### The ideal cut out on an arbitrary open subset -/

section IdealOfOpens

variable (J : X.IdealSheafData)

/-- The ideal cut out by `J` on an **arbitrary** open subset, not just an affine one: the
kernel of the restriction map to the closed subscheme.

`Scheme.IdealSheafData` itself only records ideals on affine opens, so this is the extension
of `J.ideal` to all of `X.Opens`, and `idealOfOpens_eq_ideal` says the extension is
compatible. -/
noncomputable def idealOfOpens (U : X.Opens) : Ideal Γ(X, U) :=
  RingHom.ker (J.subschemeι.app U).hom

@[simp]
lemma idealOfOpens_eq_ideal (U : X.affineOpens) : J.idealOfOpens U.1 = J.ideal U :=
  J.ker_subschemeι_app U

lemma mem_idealOfOpens_iff {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔ J.subschemeι.app U x = 0 :=
  RingHom.mem_ker

/-- **The zero ideal sheaf has no nonzero sections**: the subscheme it cuts out is all of `X`,
so the restriction to it is injective. -/
@[simp]
lemma idealOfOpens_bot (U : X.Opens) : (⊥ : X.IdealSheafData).idealOfOpens U = ⊥ :=
  (RingHom.injective_iff_ker_eq_bot _).mp
    (ConcreteCategory.bijective_of_isIso ((⊥ : X.IdealSheafData).subschemeι.app U)).injective

/-- Membership in the ideal cut out on an open subset is stable under restriction. -/
lemma map_mem_idealOfOpens {U V : X.Opens} (h : V ≤ U) {x : Γ(X, U)}
    (hx : x ∈ J.idealOfOpens U) :
    X.presheaf.map (homOfLE h).op x ∈ J.idealOfOpens V := by
  rw [mem_idealOfOpens_iff] at hx ⊢
  rw [← Hom.map_app_apply, hx, map_zero]

/-- **The ideal cut out on an arbitrary open subset is detected on the affine opens it
contains**: a section of `𝒪_X` over `U` lies in `J.idealOfOpens U` exactly when its restriction
to every affine open `V ≤ U` lies in `J.ideal V`.

This is what makes `AlgebraicGeometry.Scheme.IdealSheafData.idealOfOpens` computable from the
data recorded by `J`, which is only the family of ideals over the affine opens. -/
lemma mem_idealOfOpens_iff_forall_affineOpens {U : X.Opens} {x : Γ(X, U)} :
    x ∈ J.idealOfOpens U ↔
      ∀ (V : X.affineOpens) (h : V.1 ≤ U), X.presheaf.map (homOfLE h).op x ∈ J.ideal V := by
  refine ⟨fun hx V h ↦ ?_, fun H ↦ ?_⟩
  · rw [← idealOfOpens_eq_ideal]
    exact J.map_mem_idealOfOpens h hx
  · rw [mem_idealOfOpens_iff]
    -- the affine opens contained in `U` cover `U`, so the sheaf condition on `V(J)` applies
    refine J.subscheme.IsSheaf.section_ext fun y hy ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (u := U.1) hy U.2
    have hVU' : V ≤ U := hVU
    refine ⟨J.subschemeι ⁻¹ᵁ V, fun z hz ↦ hVU' hz, hyV, ?_⟩
    -- the two restriction maps agree because `X.Opens` has at most one morphism per pair
    have he : (homOfLE (fun z hz ↦ hVU' hz : J.subschemeι ⁻¹ᵁ V ≤ J.subschemeι ⁻¹ᵁ U)).op =
        ((Opens.map J.subschemeι.base).map (homOfLE hVU')).op := Subsingleton.elim _ _
    rw [he, map_zero, Hom.map_app_apply, ← mem_idealOfOpens_iff,
      idealOfOpens_eq_ideal J ⟨V, hV⟩]
    exact H ⟨V, hV⟩ hVU'

end IdealOfOpens

/-- **The product of two ideal sheaves multiplies sections**, over an arbitrary open subset:
if `a` is a section of `I` and `b` a section of `J` over `U` then `a * b` is a section of
`I * J` over `U`. This is `Ideal.mul_mem_mul` for ideal sheaves. -/
lemma mul_mem_mul_idealOfOpens {I J : X.IdealSheafData} {U : X.Opens} {a b : Γ(X, U)}
    (ha : a ∈ I.idealOfOpens U) (hb : b ∈ J.idealOfOpens U) :
    a * b ∈ (I * J).idealOfOpens U := by
  -- the product of ideal sheaves is recorded on the affine opens only
  rw [mem_idealOfOpens_iff_forall_affineOpens] at ha hb ⊢
  intro V h
  simp only [ideal_mul, Pi.mul_apply, map_mul]
  exact Ideal.mul_mem_mul (ha V h) (hb V h)

/-- **Two ideal sheaves whose product vanishes annihilate each other on sections**, over an
arbitrary open subset: if `I * J = 0` and `a`, `b` are sections of `𝒪_X` over `U` lying in `I`
and in `J` respectively, then `a * b = 0`. -/
lemma mul_eq_zero_of_mem_idealOfOpens {I J : X.IdealSheafData} (hIJ : I * J = 0) {U : X.Opens}
    {a b : Γ(X, U)} (ha : a ∈ I.idealOfOpens U) (hb : b ∈ J.idealOfOpens U) : a * b = 0 := by
  have hbot : I * J = ⊥ := hIJ
  have hmem := mul_mem_mul_idealOfOpens ha hb
  rwa [hbot, idealOfOpens_bot, Ideal.mem_bot] at hmem

variable (I : X.IdealSheafData) (U : X.affineOpens)

/-- The affine chart of the subscheme over an affine open is the fibre product: the
square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` and `fromSpec` is a pullback. -/
lemma isPullback_subschemeCover_map :
    IsPullback (I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))))
      I.subschemeι U.2.fromSpec := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · exact (I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)
  · rw [U.2.opensRange_fromSpec, opensRange_subschemeCover_map]

/-- **The subscheme of an ideal sheaf base changes to the subscheme of the extended
ideal.** Along a morphism `Spec S ⟶ X` of the form `Spec.map φ ≫ U.2.fromSpec` with `U` an
affine open, the base change of `I.subschemeι` is `Spec` of the quotient of `S` by the
extension of `I(U)` along `φ`. -/
lemma isPullback_subschemeι_specMap_fromSpec {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.ideal U).map φ.hom) φ.hom
        Ideal.le_comap_map)) ≫ I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ.hom))))
      I.subschemeι (Spec.map φ ≫ U.2.fromSpec) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_quotient φ (I.ideal U))).paste_horiz
      (I.isPullback_subschemeCover_map U)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open IdealSheafData in
/-- **The kernel ideal sheaf of a quasi-compact morphism consists of the functions vanishing on
the source**, over an arbitrary open subset, not merely an affine one. -/
lemma mem_idealOfOpens_ker_iff [QuasiCompact f] {U : Y.Opens} {x : Γ(Y, U)} :
    x ∈ f.ker.idealOfOpens U ↔ f.app U x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · rw [mem_idealOfOpens_iff_forall_affineOpens] at hx
    -- the preimages of the affine opens contained in `U` cover `f ⁻¹ᵁ U`
    refine X.IsSheaf.section_ext fun y hy ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (u := U.1) hy U.2
    have hVU' : V ≤ U := hVU
    refine ⟨f ⁻¹ᵁ V, fun z hz ↦ hVU' hz, hyV, ?_⟩
    -- the two restriction maps agree because `X.Opens` has at most one morphism per pair
    have he : (homOfLE (fun z hz ↦ hVU' hz : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U)).op =
        ((Opens.map f.base).map (homOfLE hVU')).op := Subsingleton.elim _ _
    rw [he, map_zero, map_app_apply]
    simpa only [ker_apply, RingHom.mem_ker] using hx ⟨V, hV⟩ hVU'
  · rw [mem_idealOfOpens_iff_forall_affineOpens]
    intro V h
    rw [ker_apply, RingHom.mem_ker, ← map_app_apply, hx, map_zero]

/-- The kernel of the map to the scheme-theoretic image is trivial: no closed subscheme of
`f.image` strictly smaller than `f.image` contains the image of `f`. -/
lemma ker_toImage [QuasiCompact f] : f.toImage.ker = ⊥ := by
  refine IdealSheafData.ext_of_iSup_eq_top
    (fun V : Y.affineOpens ↦ ⟨f.imageι ⁻¹ᵁ V.1, V.2.preimage f.imageι⟩) ?_ fun V ↦ ?_
  · rw [← preimage_iSup, iSup_affineOpens_eq_top, preimage_top]
  · rw [ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective V)

instance [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := ⟨f.ker_toImage⟩

end AlgebraicGeometry.Scheme.Hom
