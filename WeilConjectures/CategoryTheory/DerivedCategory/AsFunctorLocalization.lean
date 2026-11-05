/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
public import Mathlib.Algebra.Homology.Functor

/-!
# Levelwise localization of complexes of diagrams

For a complex `K` of diagrams `I ⥤ C`, the diagram `K.asFunctor ⋙ DerivedCategory.Q` of
localized levels only depends on the image of `K` in the derived category of diagrams: an
isomorphism `Q K ≅ Q L` induces an isomorphism of diagrams
`K.asFunctor ⋙ Q ≅ L.asFunctor ⋙ Q`. The components are the images of the isomorphism under the
exact evaluation functors.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {I : Type*} [SmallCategory I] {C : Type*} [Category C] [Abelian C]
  [HasDerivedCategory C] [HasDerivedCategory (I ⥤ C)]

end HomologicalComplex
