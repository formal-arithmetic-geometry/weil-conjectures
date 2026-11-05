/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Presentations of derived functors by additive functors

A presentation of a functor `Φ : D(C) ⥤ D(D)` by an additive functor `F : C ⥤ D` is an
isomorphism `Q ⋙ Φ ≅ F.mapHomologicalComplex ⋙ Q`. A natural transformation between
presented functors *represents* an ordinary natural transformation if both agree after
precomposition with `Q`, through the presentations. Representation is stable under
composition, whiskering and the associators, and the isomorphisms
`mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` represent their defining data.
This reduces identities of pasted derived comparisons on images of complexes to identities
of ordinary natural transformations.

Source: Stacks Project, Tag 05RU (universal property of localization) and Tag 05S7.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

namespace DerivedPresentation

end DerivedPresentation

open DerivedPresentation

namespace DerivedRepresents

variable {Φ Ψ Ξ : DerivedCategory C ⥤ DerivedCategory D} {F G H : C ⥤ D}
  [F.Additive] [G.Additive] [H.Additive]
  {p : DerivedPresentation Φ F} {q : DerivedPresentation Ψ G} {r : DerivedPresentation Ξ H}

end DerivedRepresents

section Basic

open DerivedRepresents

end Basic

end CategoryTheory.Functor
