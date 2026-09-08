/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

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

Finally, for morphisms into a scheme `Y` separated over a base `S`, agreement on the pairwise
intersections need not be assumed: by rigidity it follows from agreement on a single
scheme-theoretically dense open `D` contained in every `U i`. We record:

- `AlgebraicGeometry.Scheme.Opens.homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant` — the
  deduction of pairwise agreement from agreement on `D`;
- `AlgebraicGeometry.Scheme.Opens.glueMorphismsOfDominant` — the resulting glued morphism, with
  `AlgebraicGeometry.Scheme.Opens.homOfLE_glueMorphismsOfDominant` and
  `AlgebraicGeometry.Scheme.Opens.glueMorphismsOfDominant_comp` saying that it restricts to
  `g i` on `U i` and is a morphism over `S`.
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

section Dominant

variable {S : Scheme.{u}} (V : J → X.Opens) (D : X.Opens)

/-- Morphisms out of a family of opens into a scheme separated over `S`, agreeing on a common
scheme-theoretically dense open `D`, agree on the pairwise intersections. -/
lemma Scheme.Opens.homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) (i j : J) :
    X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ g i =
      X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ g j := by
  have := IsSchemeTheoreticallyDominant.homOfLE (le_inf (hD i) (hD j))
  refine ext_of_isSchemeTheoreticallyDominant p ?_ (X.homOfLE (le_inf (hD i) (hD j))) ?_
  · rw [Category.assoc, Category.assoc, hq i, hq j, X.homOfLE_ι_assoc, X.homOfLE_ι_assoc]
  · rw [← Category.assoc, ← Category.assoc, X.homOfLE_homOfLE, X.homOfLE_homOfLE]
    exact hg i j

/-- Glue a family of morphisms `g i : V i ⟶ Y` into a scheme separated over `S` that agree on a
common scheme-theoretically dense open `D ≤ V i`, into a morphism `(⨆ i, V i) ⟶ Y`. -/
noncomputable def Scheme.Opens.glueMorphismsOfDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) :
    (⨆ i, V i).toScheme ⟶ Y :=
  Scheme.Opens.glueMorphisms V g
    (homOfLE_comp_eq_of_le_of_isSchemeTheoreticallyDominant V D hD p q g hq hg)

@[reassoc (attr := simp)]
lemma Scheme.Opens.homOfLE_glueMorphismsOfDominant
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) (i : J) :
    X.homOfLE (le_iSup V i) ≫ glueMorphismsOfDominant V D hD p q g hq hg = g i :=
  homOfLE_glueMorphisms V g _ i

/-- The morphism glued from a family of `S`-morphisms is a morphism over `S`. -/
lemma Scheme.Opens.glueMorphismsOfDominant_comp
    (hD : ∀ i, D ≤ V i) [QuasiCompact D.ι] [IsSchemeTheoreticallyDominant D.ι]
    (p : Y ⟶ S) [IsSeparated p] (q : X ⟶ S)
    (g : ∀ i, (V i).toScheme ⟶ Y) (hq : ∀ i, g i ≫ p = (V i).ι ≫ q)
    (hg : ∀ i j, X.homOfLE (hD i) ≫ g i = X.homOfLE (hD j) ≫ g j) :
    glueMorphismsOfDominant V D hD p q g hq hg ≫ p = (⨆ i, V i).ι ≫ q := by
  refine hom_ext_iSup V _ _ fun i ↦ ?_
  rw [homOfLE_glueMorphismsOfDominant_assoc, hq i, X.homOfLE_ι_assoc]

end Dominant

end AlgebraicGeometry
