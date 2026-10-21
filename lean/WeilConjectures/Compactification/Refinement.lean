/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Over

/-!

# Refinements and composites of compactifications over a base scheme

Let `S` be a quasi-compact and quasi-separated scheme, and let `f : X ⟶ Y` be a morphism of
`Over S`, between objects whose structure morphisms are separated and of finite type. This file
records the two geometric inputs that make the lower shriek independent of the compactification
and compatible with composition.

* **Refinements.** A refinement of a compactification `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)` of `f.left` by
  a compactification `c = (X ⟶[i] Z ⟶[p] Y)` is a proper morphism `h : Z ⟶ Z₁` over `Y` such that
  the square
  ```
  X --i--> Z
  |𝟙       |h
  v        v
  X --i₁-> Z₁
  ```
  is cartesian, that is `h⁻¹(X) = X` (`Compactification.OverRefinement`). Any two
  compactifications have a common refinement (`Compactification.exists_overRefinement`): the
  scheme-theoretic closure of the image of `X` in `Z₁ ×_Y Z₂`.
* **Composites.** For compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left` and
  `c' = (Y ⟶[j] Z' ⟶[q] T)` of `g.left`, the morphism `p ≫ j : Z ⟶ Z'` has a compactification
  `d = (Z ⟶[i'] W ⟶[p'] Z')` whose square
  ```
  Z --i'--> W
  |p        |p'
  v         v
  Y --j---> Z'
  ```
  is cartesian (`Compactification.exists_isPullback_overG_overI`): the scheme-theoretic closure
  of `Z` in any compactification of `p ≫ j`. Then `X ⟶[i ≫ i'] W ⟶[p' ≫ q] T` is a
  compactification of `(f ≫ g).left` (`Compactification.overComp`).

## Sorried input

`Compactification.exists_overRefinement` and `Compactification.exists_isPullback_overG_overI`
are `sorry`ed: both need the scheme-theoretic closure of a quasi-compact immersion and its
compatibility with restriction to open subschemes.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y}

/-- A *refinement* of a compactification `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)` of `f.left` by a
compactification `c = (X ⟶[i] Z ⟶[p] Y)`: a proper morphism `h : Z ⟶ Z₁` of `Over S` over `Y`
whose square with `i` and `i₁` is cartesian, that is `h⁻¹(X) = X`. -/
structure OverRefinement (c c₁ : Compactification f.left) where
  /-- The proper morphism `h : Z ⟶ Z₁` between the compactifications. -/
  hom : c.overObj ⟶ c₁.overObj
  hom_overG : hom ≫ c₁.overG = c.overG
  isPullback : IsPullback (𝟙 X) c.overI c₁.overI hom
  isProper : IsProper hom.left

variable {T : Over S} {g : Y ⟶ T}

/-- The composite compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] T` of `(f ≫ g).left`, for
compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left`, `c' = (Y ⟶[j] Z' ⟶[q] T)` of `g.left`,
and `d = (Z ⟶[i'] W ⟶[p'] Z')` of `p ≫ j`. -/
noncomputable def overComp (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) : Compactification (f ≫ g).left where
  Z := d.Z
  g := d.g ≫ c'.g
  i := c.i ≫ d.i
  comm := by
    have hd : c.g ≫ c'.i = d.i ≫ d.g := by simpa using d.comm
    calc (f ≫ g).left = (c.i ≫ c.g) ≫ c'.i ≫ c'.g := by
          rw [Over.comp_left, ← c.comm, ← c'.comm]
      _ = (c.i ≫ d.i) ≫ d.g ≫ c'.g := by
          simp only [Category.assoc]
          rw [reassoc_of% hd]
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The object `W` of the composite compactification `overComp c c' d` is the object of `d`, up
to the associativity of the structure morphism `W ⟶ Z' ⟶ T ⟶ S`. -/
noncomputable def overCompObjIso (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overComp c c' d).overObj ≅ d.overObj :=
  Over.isoMk (Iso.refl _) (by simp [overComp, overObj])

@[reassoc (attr := simp)]
lemma overI_overCompObjIso_hom (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overComp c c' d).overI ≫ (overCompObjIso c c' d).hom = c.overI ≫ d.overI := by
  ext
  simp [overCompObjIso, overComp]

@[reassoc (attr := simp)]
lemma overCompObjIso_hom_overG (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overCompObjIso c c' d).hom ≫ d.overG ≫ c'.overG = (overComp c c' d).overG := by
  ext
  simp [overCompObjIso, overComp]

section Existence

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [CompactSpace S] [QuasiSeparatedSpace S]

/-- Any two compactifications `c₁` and `c₂` of `f.left` have a common refinement: the
scheme-theoretic closure `Z` of the image of `X` in `Z₁ ×_Y Z₂`, with the projections to `Z₁`
and `Z₂`. The immersion `X ⟶ Z₁ ×_Y Z₂` is an open immersion into its scheme-theoretic closure,
and the preimage of `X ⊆ Z₁` in `Z` is `X`, since `X` is closed in `X ×_Y Z₂` (`Z₂` is separated
over `Y`). -/
theorem exists_overRefinement (c₁ c₂ : Compactification f.left) :
    ∃ c : Compactification f.left, Nonempty (OverRefinement c c₁) ∧
      Nonempty (OverRefinement c c₂) :=
  sorry

variable [QuasiCompact T.hom] [IsSeparated T.hom]

/-- For compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left` and `c' = (Y ⟶[j] Z' ⟶[q] T)` of
`g.left`, the morphism `p ≫ j : Z ⟶ Z'` has a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')`
whose square with `p` and `j` is cartesian: the scheme-theoretic closure `W` of `Z` in any
compactification of `p ≫ j`. Then `p'⁻¹(Y)` contains `Z` as an open subscheme which is proper,
hence closed, over `Y`, and schematically dense, so that `p'⁻¹(Y) = Z`. -/
theorem exists_isPullback_overG_overI (c : Compactification f.left)
    (c' : Compactification g.left) :
    ∃ d : Compactification (c.overG ≫ c'.overI).left,
      IsPullback c.overG d.overI c'.overI d.overG :=
  sorry

end Existence

end AlgebraicGeometry.Compactification
