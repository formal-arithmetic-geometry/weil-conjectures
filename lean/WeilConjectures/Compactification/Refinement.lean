/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.Over
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.Compactification.Comp
import WeilConjectures.Compactification.Dense

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

## Proofs

The common refinement uses `Compactification.inf` and its cartesian projection squares.
For the composite, choose a dense compactification of `p ≫ j`. Its restriction over `Y`
has open immersion both closed (since `p` is proper) and scheme-theoretically dominant,
hence an isomorphism. The forgetful functor from `Over S` reflects these pullback squares.

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

/-- Transport a cartesian scheme refinement to the category over the base.
This is the construction of `overRefinementOfRefinement` in `OverRefinement`, reproduced
privately because that module imports this one. -/
private theorem nonempty_overRefinement_of_refinement {c c₁ : Compactification f.left}
    (r : c.Refinement c₁) (h : IsPullback (𝟙 X.left) c.i c₁.i r.hom) :
    Nonempty (OverRefinement c c₁) := by
  exact ⟨{
    hom := Over.homMk r.hom (by simp [overObj, reassoc_of% r.hom_g])
    hom_overG := Over.OverMorphism.ext r.hom_g
    isPullback := IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext h.w) h
    isProper := r.isProper }⟩

/-- The restriction of a dense compactification of a proper map followed by an open
immersion is an isomorphism. This is the proof of `isIso_restrict_i` in `OverRefinement`,
which cannot be imported here because it imports this module. -/
private theorem isIso_restrict_i_of_dense {A B C : Scheme.{u}} {p : A ⟶ B} {j : B ⟶ C}
    [IsProper p] [IsOpenImmersion j] (d : Compactification (p ≫ j))
    [IsSchemeTheoreticallyDominant d.i] [QuasiCompact d.i] : IsIso d.restrict.i := by
  have : IsClosedImmersion d.restrict.i :=
    d.restrict.isClosedImmersion_openImmersion inferInstance
  have : QuasiCompact (d.restrict.i ≫ pullback.fst d.g j) := by
    rw [restrict_i_fst]
    infer_instance
  have : IsSchemeTheoreticallyDominant (d.restrict.i ≫ pullback.fst d.g j) := by
    rw [restrict_i_fst]
    infer_instance
  have : IsSchemeTheoreticallyDominant d.restrict.i := .of_comp _ (pullback.fst d.g j)
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr d.restrict.i.ker_eq_bot

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
      Nonempty (OverRefinement c c₂) := by
  -- Retain the original section hypotheses, although the geometric result needs fewer.
  have _ := ‹LocallyOfFiniteType X.hom›
  have _ := ‹IsSeparated X.hom›
  have _ := ‹LocallyOfFiniteType Y.hom›
  have _ := ‹QuasiCompact Y.hom›
  have _ := ‹CompactSpace S›
  have _ := ‹QuasiSeparatedSpace S›
  have : QuasiCompact f.left := by
    have : QuasiCompact (f.left ≫ Y.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp f.left Y.hom
  exact ⟨inf c₁ c₂,
    nonempty_overRefinement_of_refinement _ (isPullback_infFst c₁ c₂).flip,
    nonempty_overRefinement_of_refinement _ (isPullback_infSnd c₁ c₂).flip⟩

variable [QuasiCompact T.hom] [IsSeparated T.hom]

/-- For compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left` and `c' = (Y ⟶[j] Z' ⟶[q] T)` of
`g.left`, the morphism `p ≫ j : Z ⟶ Z'` has a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')`
whose square with `p` and `j` is cartesian: the scheme-theoretic closure `W` of `Z` in any
compactification of `p ≫ j`. Then `p'⁻¹(Y)` contains `Z` as an open subscheme which is proper,
hence closed, over `Y`, and schematically dense, so that `p'⁻¹(Y) = Z`. -/
theorem exists_isPullback_overG_overI (c : Compactification f.left)
    (c' : Compactification g.left) :
    ∃ d : Compactification (c.overG ≫ c'.overI).left,
      IsPullback c.overG d.overI c'.overI d.overG := by
  -- Retain the original section hypotheses, although the geometric result needs fewer.
  have _ := ‹LocallyOfFiniteType X.hom›
  have _ := ‹QuasiCompact X.hom›
  have _ := ‹IsSeparated X.hom›
  have _ := ‹LocallyOfFiniteType Y.hom›
  have _ := ‹IsSeparated Y.hom›
  have : QuasiCompact g.left := by
    have : QuasiCompact (g.left ≫ T.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp g.left T.hom
  have : QuasiCompact c'.i := c'.quasiCompact_openImmersion inferInstance
  have : CompactSpace c'.Z := QuasiCompact.compactSpace_of_compactSpace (c'.g ≫ T.hom)
  have : QuasiSeparatedSpace c'.Z := quasiSeparatedSpace_of_quasiSeparated (c'.g ≫ T.hom)
  obtain ⟨d, hd⟩ := exists_isDense_compactification (c.g ≫ c'.i)
  have : IsSchemeTheoreticallyDominant d.i := hd
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  have := isIso_restrict_i_of_dense d
  have hs : IsPullback c.g d.i c'.i d.g := by
    refine d.isPullback_restrict.of_iso (asIso d.restrict.i).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp [d.restrict.comm]
    · simp
  exact ⟨d, IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext d.comm) hs⟩

end Existence

end AlgebraicGeometry.Compactification
