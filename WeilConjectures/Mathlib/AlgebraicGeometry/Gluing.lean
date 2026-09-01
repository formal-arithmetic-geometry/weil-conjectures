/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing morphisms defined on a family of opens

Mathlib glues morphisms defined on the members of an open cover, with the compatibility
hypothesis stated as an equality of the two projections out of a fibre product. For a family
of opens `U : J → X.Opens` the fibre product of `U i` and `U j` over `⨆ i, U i` is the
intersection `U i ⊓ U j`, so the hypothesis takes the more elementary form of agreement on
the pairwise intersections. We record this form:

- `AlgebraicGeometry.Scheme.Opens.glueMorphisms` — the glued morphism `(⨆ i, U i) ⟶ Y`;
- `AlgebraicGeometry.Scheme.Opens.homOfLE_glueMorphisms` — it restricts to `f i` on `U i`;
- `AlgebraicGeometry.Scheme.Opens.hom_ext_iSup` — two morphisms out of `⨆ i, U i` agreeing on
  every `U i` are equal.

For a family of opens covering `X`, i.e. with `⨆ i, U i = ⊤`, we also record the corresponding
`AlgebraicGeometry.Scheme.Opens.glueMorphismsOfTop`, `Scheme.Opens.ι_glueMorphismsOfTop` and
`AlgebraicGeometry.Scheme.Opens.hom_ext_of_iSup_eq_top`, gluing to a morphism `X ⟶ Y`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {J : Type*} {X Y : Scheme.{u}} (U : J → X.Opens)

/-- Morphisms `f i : U i ⟶ Y` that agree on the pairwise intersections `U i ⊓ U j` are
compatible in the sense of `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, i.e. they agree on
the fibre products of the members of `Scheme.Opens.iSupOpenCover U`. -/
lemma Scheme.Opens.pullback_fst_comp_eq_snd_comp (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i j : J) :
    pullback.fst (X.homOfLE (le_iSup U i)) (X.homOfLE (le_iSup U j)) ≫ f i =
      pullback.snd _ _ ≫ f j := by
  rw [← cancel_epi (isPullback_opens_inf_le (le_iSup U i) (le_iSup U j)).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact hf i j

/-- Glue a family of morphisms `f i : U i ⟶ Y` that agree on the pairwise intersections
`U i ⊓ U j` into a morphism `(⨆ i, U i) ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphisms (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    (⨆ i, U i).toScheme ⟶ Y :=
  (iSupOpenCover U).glueMorphisms f (Scheme.Opens.pullback_fst_comp_eq_snd_comp U f hf)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphisms (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : J) :
    X.homOfLE (le_iSup U i) ≫ Scheme.Opens.glueMorphisms U f hf = f i :=
  (iSupOpenCover U).ι_glueMorphisms f _ i

/-- Two morphisms out of `⨆ i, U i` that agree on every `U i` are equal. -/
lemma Scheme.Opens.hom_ext_iSup (g₁ g₂ : (⨆ i, U i).toScheme ⟶ Y)
    (h : ∀ i, X.homOfLE (le_iSup U i) ≫ g₁ = X.homOfLE (le_iSup U i) ≫ g₂) : g₁ = g₂ :=
  (iSupOpenCover U).hom_ext g₁ g₂ h

/-- Glue a family of morphisms `f i : U i ⟶ Y` defined on a family of opens covering `X` and
agreeing on the pairwise intersections `U i ⊓ U j` into a morphism `X ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphismsOfTop (hU : ⨆ i, U i = ⊤)
    (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) :
    X ⟶ Y :=
  (X.isoOfEq hU ≪≫ X.topIso).inv ≫ Scheme.Opens.glueMorphisms U f hf

@[reassoc (attr := simp)]
lemma Scheme.Opens.ι_glueMorphismsOfTop (hU : ⨆ i, U i = ⊤) (f : ∀ i, (U i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ f i =
      X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ f j) (i : J) :
    (U i).ι ≫ Scheme.Opens.glueMorphismsOfTop U hU f hf = f i := by
  have hhom : (X.isoOfEq hU ≪≫ X.topIso).hom = (⨆ i, U i).ι := by simp
  rw [glueMorphismsOfTop, ← X.homOfLE_ι (le_iSup U i), ← hhom, Category.assoc,
    Iso.hom_inv_id_assoc, homOfLE_glueMorphisms]

/-- Two morphisms out of `X` that agree on every member of a family of opens covering `X` are
equal. -/
lemma Scheme.Opens.hom_ext_of_iSup_eq_top (hU : ⨆ i, U i = ⊤) (g₁ g₂ : X ⟶ Y)
    (h : ∀ i, (U i).ι ≫ g₁ = (U i).ι ≫ g₂) : g₁ = g₂ := by
  have hhom : (X.isoOfEq hU ≪≫ X.topIso).hom = (⨆ i, U i).ι := by simp
  rw [← cancel_epi (X.isoOfEq hU ≪≫ X.topIso).hom]
  refine hom_ext_iSup U _ _ fun i ↦ ?_
  rw [hhom, X.homOfLE_ι_assoc, X.homOfLE_ι_assoc, h]

end AlgebraicGeometry
