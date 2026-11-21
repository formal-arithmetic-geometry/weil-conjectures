/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.Over
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Base change of compactifications in the six-functor setting

The compactification and its base change are the existing constructions. Objects of
`Over (Spec (.of k))` and their morphisms retain all the structure maps over the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

set_option linter.unusedVariables false in
/-- Base change of a quasi-compact compactification along a cartesian square of separated
finite-type schemes over the field remains in that setting. The induced open arrow is
unique, both component squares are cartesian, and the new proper arrow and open immersion
form the existing base-changed compactification. All three new arrows are over `k`:
`overBaseChangeFst`, `overI` and `overG` are morphisms of `Over (Spec (.of k))`. -/
theorem baseChange_compactification_in_setting
    (ℓ p₀ : ℕ) (hℓ : ℓ.Prime) (k : Type u) [Field k] [CharP k p₀]
    (hp₀ : 0 < p₀) (hp₀ℓ : p₀ ≠ ℓ)
    {X X' Y Y' : Over (Spec (.of k))}
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) (c : BoundaryCompactification f.left) :
    (∃! j : X' ⟶ (c.obj.obj.ofIsPullback sq.overLeft).overObj,
      j ≫ c.obj.obj.overBaseChangeFst sq = g' ≫ c.obj.obj.overI ∧
      j ≫ (c.obj.obj.ofIsPullback sq.overLeft).overG = f') ∧
    (c.obj.obj.ofIsPullback sq.overLeft).overI ≫
      (c.obj.obj.ofIsPullback sq.overLeft).overG = f' ∧
    IsPullback g' (c.obj.obj.ofIsPullback sq.overLeft).overI
      c.obj.obj.overI (c.obj.obj.overBaseChangeFst sq) ∧
    IsPullback (c.obj.obj.overBaseChangeFst sq)
      (c.obj.obj.ofIsPullback sq.overLeft).overG c.obj.obj.overG g ∧
    QuasiCompact (c.obj.obj.ofIsPullback sq.overLeft).i ∧
    IsOpenImmersion (c.obj.obj.ofIsPullback sq.overLeft).i ∧
    IsProper (c.obj.obj.ofIsPullback sq.overLeft).g ∧
    IsSeparated (c.obj.obj.ofIsPullback sq.overLeft).overObj.hom ∧
    LocallyOfFiniteType (c.obj.obj.ofIsPullback sq.overLeft).overObj.hom ∧
    QuasiCompact (c.obj.obj.ofIsPullback sq.overLeft).overObj.hom ∧
    IsSeparated c.obj.obj.overObj.hom ∧
    LocallyOfFiniteType c.obj.obj.overObj.hom ∧
    QuasiCompact c.obj.obj.overObj.hom := by
  have hfst : (c.obj.obj.ofIsPullback sq.overLeft).overI ≫
      c.obj.obj.overBaseChangeFst sq = g' ≫ c.obj.obj.overI :=
    Over.OverMorphism.ext (c.obj.obj.ofIsPullback_i_fst sq.overLeft)
  have hcomp := (c.obj.obj.ofIsPullback sq.overLeft).overI_overG
  have hproper := c.obj.obj.overBaseChange_isPullback_g sq
  refine ⟨?_, hcomp, c.obj.obj.overBaseChange_isPullback_i sq, hproper,
    ?_, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩
  · refine ⟨(c.obj.obj.ofIsPullback sq.overLeft).overI, ⟨hfst, hcomp⟩, ?_⟩
    intro j hj
    exact hproper.hom_ext (hj.1.trans hfst.symm) (hj.2.trans hcomp.symm)
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (c.obj.obj.isPullback_i_ofIsPullback sq.overLeft) c.obj.property

end AlgebraicGeometry.Compactification
