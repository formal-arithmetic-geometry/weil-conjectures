/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Yoneda

/-!
# Brown representability for cohomological functors

Source: Stacks Project, Derived Categories, Tag 0A8F, Lemma `lemma-brown`
(blueprint: lem-pc-brown-cohomological-representability).
-/

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{v} C]

/-- (blueprint: lem-pc-brown-cohomological-representability) Every cohomological
functor on a compactly generated triangulated category that
converts coproducts to products is represented by an object. Set-indexed means
indexed by `Type v`, the universe of the morphism sets of `C`.

This is Brown representability (Stacks Project, Tag 0A8F, Lemma `lemma-brown`;
blueprint: lem-pc-brown-cohomological-representability). The hypotheses say that
`C` is compactly generated, that `H` is homological on `Cᵒᵖ` (the contravariant
cohomological condition), and that `H` preserves all discrete limits, which are
the products corresponding to set-indexed coproducts in `C`. The conclusion is
the natural additive Yoneda isomorphism `H ≅ preadditiveYoneda.obj G`.
-/
theorem brownCohomologicalRepresentability
    (hC : IsCompactlyGeneratedTriangulated.{v} C)
    (H : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ (I : Type v), PreservesLimitsOfShape (Discrete I) H) :
    ∃ G : C, Nonempty (H ≅ preadditiveYoneda.obj G) := by
  sorry

end CategoryTheory
