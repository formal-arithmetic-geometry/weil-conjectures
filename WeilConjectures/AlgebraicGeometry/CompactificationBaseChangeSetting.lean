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
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Base change of compactifications in the six-functor setting

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-shriek-base-change-morphism-compactification.md,
clauses 1--3 (blueprint: det-def-sfb-shriek-base-change-morphism-compactification).

The compactification and its base change are the existing constructions. Objects of
`Over (Spec (.of k))` and their morphisms retain all the structure maps over the field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

/-- Base change of a quasi-compact compactification along a cartesian square of separated
finite-type schemes over the field remains in that setting. The induced open arrow is
unique, both component squares are cartesian, and the new proper arrow and open immersion
form the existing base-changed compactification. All three new arrows are over `k`:
`overBaseChangeFst`, `overI` and `overG` are morphisms of `Over (Spec (.of k))`.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-open-coefficients/det-def-sfb-shriek-base-change-morphism-compactification.md,
clauses 1--3 (blueprint: det-def-sfb-shriek-base-change-morphism-compactification).

Proof plan, following the node's five steps:
1. The factorization `c.comm` and the given cartesian square make the pair `(g' ≫ i, f')`
compatible. The universal property of `def-pc-fibre-product` gives its unique lift, namely
`ofIsPullback`. The proper square is the defining pullback. Cancel that square from the
outer cartesian rectangle using `lem-weil-pbc-cartesian-square-pasting` to obtain the open
square. This uses `sk-def-nagata-sketch-data`.
2. Apply `lem-weil-pbc-open-immersion-base-change` and `lem-weil-pbc-proper-base-change`
to these two squares. Neither application needs a flatness hypothesis.
3. Give each middle scheme the composite structure map through the target. The projection
equation, `Over.w g`, and the factorization show that all arrows are over the field,
exactly as in `def-weil-scheme-over-base`.
4. Properness implies separatedness and finite type (`def-weil-proper-morphism`). Compose
with the structure maps of `Y` and `Y'`, using clause (e) of
`lem-weil-pbc-proper-fp-permanence` and clause (1) of
`lem-sfb-finite-type-composition-base-change`. Both middle schemes are consequently
separated and of finite type over `k`.
5. Apply clause (b) of `lemma-nagata-finite-type-to-separated-target` to the induced open
arrow and the new middle scheme's separated structure map. Its composite is the finite-type
structure map of `X'`, so the induced arrow is quasi-compact. Along with step 2 and the
factorization, this is the compactification of `sk-def-nagata-sketch-data`, obtained by
`def-nagata-compactification-base-change`.
-/
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
  sorry

end AlgebraicGeometry.Compactification
