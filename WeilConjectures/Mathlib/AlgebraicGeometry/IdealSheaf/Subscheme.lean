/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Complements on the subscheme cut out by an ideal sheaf

This file adds six complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.

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

## The stalk of an ideal sheaf

The germs at a point `x` of the sections of `𝒪_X` lying in an ideal sheaf `J` form an ideal
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal` of the local ring `𝒪_{X, x}`. For the kernel
ideal sheaf of a quasi-compact morphism `f` with `f.base` inducing — an immersion, for instance —
it is the kernel of the induced map of local rings
(`AlgebraicGeometry.Scheme.Hom.ker_stalkIdeal`).

The stalk ideal is computed on any single affine open `U` containing `x`: it is the extension of
`J(U)` along the germ map (`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ`),
because the ideals of an ideal sheaf on two nested affine opens are related by extension
(`Scheme.IdealSheafData.map_ideal`). On an affine scheme this reads off the stalk ideal of the
kernel ideal sheaf of `Spec φ` as the extension of `ker φ`
(`AlgebraicGeometry.Scheme.Hom.stalkIdeal_ker_specMap`).

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

## Reducedness and irreducibility of the subscheme cut out by an ideal sheaf

The subscheme `V(J)` cut out by an ideal sheaf `J` is reduced exactly when `J` is radical
(`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_iff_radical_eq`): both sides are
affine-local, and over an affine open `U` the subscheme is `Spec (Γ(X, U) ⧸ J(U))`, which is
reduced exactly when `J(U)` is a radical ideal. Equivalently, `J` is then the vanishing ideal
sheaf of its own support
(`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_iff_eq_vanishingIdeal`), so the
reduced closed subschemes of `X` are exactly the ones cut out by a vanishing ideal sheaf. The
underlying space of `V(J)` *is* the support of `J`, by construction, so `V(J)` is irreducible
exactly when the support is
(`AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme_iff_isIrreducible_support`)
and has the Krull dimension of the support
(`AlgebraicGeometry.Scheme.IdealSheafData.topologicalKrullDim_subscheme`). Putting the two
together, `V(J)` is integral exactly when `J` is radical with irreducible support
(`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_iff`).

## The reduced induced closed subscheme on a closed subset

Mathlib defines the vanishing ideal sheaf `IdealSheafData.vanishingIdeal Z` of a closed subset
`Z` of `X` and the closed subscheme `(vanishingIdeal Z).subscheme` it cuts out — the *reduced
induced closed subscheme structure* on `Z` — but records nothing about its reducedness. The
vanishing ideal sheaf is radical, so the subscheme is indeed reduced; its underlying space is
`Z`, so the subscheme is integral exactly when `Z` is irreducible
(`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_iff`) and has the
Krull dimension of `Z`
(`AlgebraicGeometry.Scheme.IdealSheafData.topologicalKrullDim_subscheme_vanishingIdeal`).

This is not the subscheme structure `Scheme.irreducibleComponent` that Mathlib puts on an
irreducible component: that one is cut out by the kernel of the restriction to the complement
of the other components, is defined for Noetherian schemes only, and is deliberately not
reduced in general, whereas the statements below apply to an arbitrary closed subset of an
arbitrary scheme.

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
- `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal`
- `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_map_germ`
- `AlgebraicGeometry.Scheme.Hom.ker_stalkIdeal`
- `AlgebraicGeometry.Scheme.Hom.stalkIdeal_ker_specMap`
- `AlgebraicGeometry.Scheme.IdealSheafData.mul_mem_mul_idealOfOpens`
- `AlgebraicGeometry.Scheme.Hom.mem_idealOfOpens_ker_iff`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeCover_map`
- `AlgebraicGeometry.Scheme.IdealSheafData.isPullback_subschemeι_specMap_fromSpec`
- `AlgebraicGeometry.Scheme.Hom.ker_toImage`
- `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_iff_radical_eq`
- `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_iff_eq_vanishingIdeal`
- `AlgebraicGeometry.Scheme.IdealSheafData.irreducibleSpace_subscheme_iff_isIrreducible_support`
- `AlgebraicGeometry.Scheme.IdealSheafData.topologicalKrullDim_subscheme`
- `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_iff`
- `AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_iff`
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

/-! ### The stalk of an ideal sheaf -/

section Stalk

variable (J : X.IdealSheafData)

/-- **The stalk of an ideal sheaf at a point**, as an ideal of the local ring `𝒪_{X, x}`: the
germs at `x` of the sections of `𝒪_X` lying in `J`.

This is the image in `𝒪_{X, x}` of the stalk of `J` viewed as a sheaf of modules; see
`AlgebraicGeometry.Scheme.IdealSheafData.mem_range_stalkMap_toModulesι_iff`. -/
noncomputable def stalkIdeal (x : X) : Ideal (X.presheaf.stalk x) where
  carrier := {r | ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
    s ∈ J.idealOfOpens U ∧ X.presheaf.germ U x hx s = r}
  add_mem' {a b} := by
    rintro ⟨U, hU, s, hs, rfl⟩ ⟨V, hV, t, ht, rfl⟩
    refine ⟨U ⊓ V, ⟨hU, hV⟩, X.presheaf.map (homOfLE inf_le_left).op s +
      X.presheaf.map (homOfLE inf_le_right).op t,
      add_mem (J.map_mem_idealOfOpens inf_le_left hs) (J.map_mem_idealOfOpens inf_le_right ht),
      ?_⟩
    rw [map_add, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
  zero_mem' := ⟨⊤, trivial, 0, zero_mem _, map_zero _⟩
  smul_mem' c {a} := by
    rintro ⟨U, hU, s, hs, rfl⟩
    obtain ⟨V, hV, b, rfl⟩ := X.presheaf.exists_germ_eq c
    refine ⟨U ⊓ V, ⟨hU, hV⟩, X.presheaf.map (homOfLE inf_le_right).op b *
      X.presheaf.map (homOfLE inf_le_left).op s,
      Ideal.mul_mem_left _ _ (J.map_mem_idealOfOpens inf_le_left hs), ?_⟩
    rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, smul_eq_mul]

lemma mem_stalkIdeal_iff (x : X) (r : X.presheaf.stalk x) :
    r ∈ J.stalkIdeal x ↔ ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)),
      s ∈ J.idealOfOpens U ∧ X.presheaf.germ U x hx s = r :=
  Iff.rfl

lemma germ_mem_stalkIdeal (x : X) {U : X.Opens} (hx : x ∈ U) {s : Γ(X, U)}
    (hs : s ∈ J.idealOfOpens U) :
    X.presheaf.germ U x hx s ∈ J.stalkIdeal x :=
  ⟨U, hx, s, hs, rfl⟩

/-- **The stalk of an ideal sheaf is computed on a single affine open**: for any affine open
`U` containing `x`, the stalk ideal at `x` is the extension of `J(U)` along the germ map
`Γ(X, U) ⟶ 𝒪_{X, x}`. Every germ at `x` of a section of `J` is a germ of a section over a
smaller affine open `V'` of `U`, along the triangle

```
  Γ(X, U) ───── res ─────▶ Γ(X, V')
        ╲                    │
         ╲ germ U x          │ germ V' x
          ╲                  ▼
           ────────────────▶ 𝒪_{X, x}
```
-/
lemma stalkIdeal_eq_map_germ (x : X) (U : X.affineOpens) (hx : x ∈ U.1) :
    J.stalkIdeal x = (J.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  refine le_antisymm ?_ ?_
  -- the definition of `stalkIdeal` ranges over all opens containing `x`; cut the family down to
  -- one affine open, using that the ideals on two nested affine opens are related by extension
  · rintro _ ⟨V, hxV, s, hs, rfl⟩
    -- shrink `V` to an affine open `V'` contained in `U` as well
    obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (u := (V ⊓ U.1 : X.Opens))
        ⟨hxV, hx⟩ (V ⊓ U.1).2
    have hVU' : (V' : X.Opens) ≤ V ⊓ U.1 := hVU
    have h1 : (⟨V', hV'⟩ : X.affineOpens) ≤ U := hVU'.trans inf_le_right
    have hmem : X.presheaf.map (homOfLE (hVU'.trans inf_le_left)).op s ∈ J.ideal ⟨V', hV'⟩ := by
      rw [← idealOfOpens_eq_ideal]
      exact J.map_mem_idealOfOpens _ hs
    rw [← map_ideal J h1] at hmem
    rw [← X.presheaf.germ_res_apply (homOfLE (hVU'.trans inf_le_left)) x hxV' s,
      ← X.presheaf.germ_res (homOfLE h1) x hxV', CommRingCat.hom_comp, ← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hmem
  · exact Ideal.map_le_iff_le_comap.mpr fun s hs ↦
      J.germ_mem_stalkIdeal x hx (by rwa [idealOfOpens_eq_ideal])

end Stalk

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

/-! ### Base change of the subscheme cut out by an ideal sheaf -/

section BaseChange

variable (I : X.IdealSheafData) (U : X.affineOpens)

/-- The affine chart of the subscheme over an affine open is the fibre product: the
square with the chart `Spec (Γ(X, U) ⧸ I(U)) ⟶ V(I)` and `fromSpec` is a pullback.

```
Spec (Γ(X, U) ⧸ I(U)) ── subschemeCover.f U ──▶ V(I)
         │                                       │
         │ Spec (Ideal.Quotient.mk (I.ideal U))  │ subschemeι
         ▼                                       ▼
     Spec Γ(X, U) ──────── U.2.fromSpec ───────▶ X
```
-/
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
extension of `I(U)` along `φ`.

```
 Spec (S ⧸ I(U)·S) ─── Spec (quotientMap …) ≫ subschemeCover.f U ──▶ V(I)
         │                                                            │
         │ Spec (Ideal.Quotient.mk ((I.ideal U).map φ))               │ subschemeι
         ▼                                                            ▼
     Spec S ──────────── Spec.map φ ≫ U.2.fromSpec ─────────────────▶ X
```
-/
lemma isPullback_subschemeι_specMap_fromSpec {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.ideal U).map φ.hom) φ.hom
        Ideal.le_comap_map)) ≫ I.subschemeCover.f U)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((I.ideal U).map φ.hom))))
      I.subschemeι (Spec.map φ ≫ U.2.fromSpec) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_quotient φ (I.ideal U))).paste_horiz
      (I.isPullback_subschemeCover_map U)

end BaseChange

/-! ### Reducedness and irreducibility of the subscheme cut out by an ideal sheaf -/

section ReducedIrreducible

variable {J : X.IdealSheafData}

/-- **The subscheme cut out by an ideal sheaf is reduced exactly when the ideal sheaf is
radical.** Both statements are affine-local: over an affine open `U` the subscheme is
`Spec (Γ(X, U) ⧸ J(U))`, which is reduced exactly when `J(U)` is a radical ideal. -/
lemma isReduced_subscheme_iff_radical_eq : IsReduced J.subscheme ↔ J.radical = J := by
  rw [IsReduced.iff_of_openCover _ J.subschemeCover.openCover, IdealSheafData.ext_iff, funext_iff]
  -- the chart of the subscheme over `U` is `Spec (Γ(X, U) ⧸ J(U))`; `change`, not `show`,
  -- because the goal genuinely changes (`linter.style.show`)
  change (∀ U : X.affineOpens, IsReduced (Spec (.of (Γ(X, U.1) ⧸ J.ideal U)))) ↔ _
  exact forall_congr' fun U ↦ by
    rw [affine_isReduced_iff, radical_ideal, Ideal.radical_eq_iff,
      Ideal.isRadical_iff_quotient_reduced]

-- The two statements below are `rfl`-level because the carrier of `J.subscheme` *is*
-- `↥J.support`: `IdealSheafData.subscheme` is the restriction of the glued space along the
-- homeomorphism `gluedHomeo`, which Mathlib marks as implementation detail. A refactor of that
-- implementation would break these two proofs, and nothing else here.
/-- **The subscheme cut out by an ideal sheaf is irreducible exactly when its support is.**
The underlying space of `V(J)` *is* the support of `J`, by construction. -/
lemma irreducibleSpace_subscheme_iff_isIrreducible_support :
    IrreducibleSpace J.subscheme ↔ IsIrreducible (J.support : Set X) :=
  isIrreducible_iff_irreducibleSpace.symm

/-- **The Krull dimension of the subscheme cut out by an ideal sheaf is that of its
support**, whose underlying space it is. -/
lemma topologicalKrullDim_subscheme :
    topologicalKrullDim J.subscheme = topologicalKrullDim (J.support : Set X) := rfl

/-- **The subscheme cut out by an ideal sheaf is integral exactly when the ideal sheaf is
radical with irreducible support**: it is reduced exactly when the ideal sheaf is radical, and
irreducible exactly when the support is, its underlying space being the support. -/
lemma isIntegral_subscheme_iff :
    IsIntegral J.subscheme ↔ J.radical = J ∧ IsIrreducible (J.support : Set X) := by
  rw [isIntegral_iff_irreducibleSpace_and_isReduced,
    irreducibleSpace_subscheme_iff_isIrreducible_support, isReduced_subscheme_iff_radical_eq,
    and_comm]

/-- **The reduced closed subschemes of `X` are exactly the ones cut out by a vanishing ideal
sheaf.** Since the vanishing ideal sheaf of a closed subset has that subset as its support,
this says that `(vanishingIdeal Z).subscheme` is the unique reduced closed subscheme with
underlying space `Z`. -/
lemma isReduced_subscheme_iff_eq_vanishingIdeal :
    IsReduced J.subscheme ↔ J = vanishingIdeal J.support := by
  rw [isReduced_subscheme_iff_radical_eq, vanishingIdeal_support, eq_comm]

/-- The subscheme cut out by the radical of an ideal sheaf is reduced. -/
instance isReduced_subscheme_radical : IsReduced J.radical.subscheme :=
  isReduced_subscheme_iff_radical_eq.mpr J.radical_radical

end ReducedIrreducible

/-! ### The reduced induced closed subscheme on a closed subset -/

section VanishingIdeal

variable {Z : Closeds X}

/-- The reduced induced closed subscheme structure on a closed subset `Z` of `X`, namely the
subscheme cut out by the vanishing ideal sheaf of `Z`, is reduced. -/
instance isReduced_subscheme_vanishingIdeal : IsReduced (vanishingIdeal Z).subscheme :=
  isReduced_subscheme_iff_radical_eq.mpr (radical_vanishingIdeal Z)

/-- **The reduced induced closed subscheme on a closed subset is integral exactly when the
subset is irreducible.** The closed subscheme `(vanishingIdeal Z).subscheme ⟶ X` cut out by
the vanishing ideal sheaf of a closed subset `Z` has underlying space `Z`, and it is reduced
because the vanishing ideal sheaf is radical. -/
lemma isIntegral_subscheme_vanishingIdeal_iff :
    IsIntegral (vanishingIdeal Z).subscheme ↔ IsIrreducible (Z : Set X) := by
  simp [isIntegral_subscheme_iff]

/-- **The reduced induced closed subscheme on a closed subset has the Krull dimension of that
subset**, whose underlying space it is. -/
lemma topologicalKrullDim_subscheme_vanishingIdeal :
    topologicalKrullDim (vanishingIdeal Z).subscheme = topologicalKrullDim (Z : Set X) := rfl

end VanishingIdeal

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

open IdealSheafData in
/-- **The stalk of the kernel ideal sheaf of a morphism inducing a topological embedding is the
kernel of the induced map of local rings.** A closed immersion, or more generally an immersion,
supplies the two hypotheses. -/
lemma ker_stalkIdeal [QuasiCompact f] (hf : Topology.IsInducing f.base) (x : X) :
    f.ker.stalkIdeal (f.base x) = RingHom.ker (f.stalkMap x).hom := by
  ext r
  constructor
  · rintro ⟨U, hx, s, hs, rfl⟩
    rw [RingHom.mem_ker]
    change f.stalkMap x (Y.presheaf.germ U (f.base x) hx s) = 0
    rw [Scheme.Hom.germ_stalkMap_apply, f.mem_idealOfOpens_ker_iff.mp hs, map_zero]
  · intro hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq r
    -- a germ killed by `f.stalkMap x` is killed by a section over some open subset `W` of `X`
    rw [Scheme.Hom.germ_stalkMap_apply,
      ← map_zero (ConcreteCategory.hom (X.presheaf.germ ⊤ x trivial))] at hr
    obtain ⟨W, hW, iWU, _, he⟩ := X.presheaf.germ_eq x hx _ _ _ hr
    rw [map_zero] at he
    -- and `W` is the preimage of an open subset `t` of `Y` because `f.base` is inducing
    obtain ⟨t, ht, htW⟩ := hf.isOpen_iff.mp W.2
    have hxt : f.base x ∈ (⟨t, ht⟩ : Y.Opens) := htW.ge hW
    have hU' : U ⊓ (⟨t, ht⟩ : Y.Opens) ≤ U := inf_le_left
    have hfU' : (f ⁻¹ᵁ (U ⊓ (⟨t, ht⟩ : Y.Opens))) ≤ W := fun z hz ↦ htW.le hz.2
    refine ⟨U ⊓ (⟨t, ht⟩ : Y.Opens), ⟨hx, hxt⟩, Y.presheaf.map (homOfLE hU').op s, ?_, ?_⟩
    · rw [f.mem_idealOfOpens_ker_iff, ← Scheme.Hom.map_app_apply f hU' s]
      -- the two restriction maps agree because `X.Opens` has at most one morphism per pair
      have hj : ((Opens.map f.base).map (homOfLE hU')).op = iWU.op ≫ (homOfLE hfU').op :=
        Subsingleton.elim _ _
      rw [hj, X.presheaf.map_comp, CommRingCat.comp_apply, he, map_zero]
    · rw [Y.presheaf.germ_res_apply]

open IdealSheafData in
/-- **The stalk of the kernel ideal sheaf of a morphism of affine schemes is the extension of
the kernel of the ring map.** No hypothesis on `φ` is needed, and `y` may be any point of
`Spec R`, not just the closed one. This extends the square of
`AlgebraicGeometry.Scheme.Hom.ker_appTop_specMap` by the germ map at `y`:

```
      R ─────────── φ ──────────────▶ S
      │                               │
      │ (ΓSpecIso R).inv              │ (ΓSpecIso S).inv
      ▼                               ▼
Γ(Spec R, ⊤) ─(Spec φ).appTop─▶ Γ(Spec S, ⊤)
      │
      │ germ ⊤ y
      ▼
𝒪_{Spec R, y}
```
-/
lemma stalkIdeal_ker_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (y : Spec R) :
    (Spec.map φ).ker.stalkIdeal y =
      (RingHom.ker φ.hom).map
        ((ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ y trivial).hom := by
  rw [stalkIdeal_eq_map_germ _ y ⟨⊤, isAffineOpen_top (Spec R)⟩ trivial,
    ideal_top_ker_specMap, Ideal.map_map, ← CommRingCat.hom_comp]

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
