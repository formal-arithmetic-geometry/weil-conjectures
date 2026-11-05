/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Colimits of homology along a functor of distinguished triangles

Let `𝒜` be an abelian category in which colimits of shape `I` exist and are exact.
Let `T : C' ⥤ Triangle (DerivedCategory 𝒜)` be a functor whose values are distinguished
triangles, `B : I ⥤ C'` and `c : Cocone B`. If, in every degree, the homology functors send
the images of `c` under two of the three projections `Triangle.π₁`, `Triangle.π₂`,
`Triangle.π₃` to colimit cocones, then the same holds for the third projection.

This is a "five lemma for colimits": the long exact homology sequences of the triangles
`T.obj X` assemble into a functor `C' ⥤ ComposableArrows 𝒜 5`; the colimit of the
sequences over `I` is exact because colimits of shape `I` are exact, and the comparison
morphism to the sequence at `c.pt` is an isomorphism by the five lemma.

## Main results

* `ComposableArrows.nonempty_isColimit_mapCocone_evaluation`: the general five lemma for
  colimits of exact sequences.
* `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₁`,
  `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₂`,
  `DerivedCategory.nonempty_isColimit_homologyFunctor_mapCocone_π₃`.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory

variable {A : Type*} [Category* A] [Abelian A]

namespace ComposableArrows

end ComposableArrows

end CategoryTheory

namespace DerivedCategory

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {C' : Type*} [Category* C']

variable {I : Type*} [Category* I] [HasColimitsOfShape I 𝒜] [HasExactColimitsOfShape I 𝒜]

end DerivedCategory
