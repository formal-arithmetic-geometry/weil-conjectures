module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.Over
public import WeilConjectures.Compactification.CommonRefinement

/-! Declarations of ours that lived in the upstream file `WeilConjectures.Compactification.Refinement` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

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

variable {T : Over S} {g : Y ⟶ T}

section Existence

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [CompactSpace S] [QuasiSeparatedSpace S]

private noncomputable def overRefinementOfRefinement
    {c c₁ : Compactification f.left} (r : c.Refinement c₁)
    (h : IsPullback (𝟙 X.left) c.i c₁.i r.hom) : OverRefinement c c₁ where
  hom := Over.homMk r.hom (by simp [overObj, reassoc_of% r.hom_g])
  hom_overG := Over.OverMorphism.ext r.hom_g
  isPullback := IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext h.w) h
  isProper := r.isProper

set_option linter.unusedSectionVars false in
variable [QuasiCompact T.hom] [IsSeparated T.hom]

end Existence

end AlgebraicGeometry.Compactification
