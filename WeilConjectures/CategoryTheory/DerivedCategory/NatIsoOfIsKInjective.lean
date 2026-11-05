/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact

/-!
# Natural isomorphisms out of a derived category, from K-injective complexes

Let `C` be an abelian category with K-injective resolutions. Every object of the derived category
`D(C)` is the image of a K-injective complex, and every morphism between images of K-injective
complexes is the image of a morphism of complexes. Hence a natural isomorphism between two
functors `F G : D(C) ⥤ E` is given by isomorphisms `F (Q I) ≅ G (Q I)` for the K-injective
complexes `I`, natural with respect to the morphisms of complexes between them
(`DerivedCategory.natIsoOfIsKInjective`).
-/

@[expose] public section

open CategoryTheory Abelian

namespace DerivedCategory

variable {C E : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] [Category E]

end DerivedCategory
