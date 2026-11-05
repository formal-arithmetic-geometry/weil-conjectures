/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Cocycle conditions for the functors induced on derived categories

For exact functors `F : C ⥤ D`, `G : D ⥤ E`, `H : C ⥤ E` between abelian categories and an
isomorphism `γ : F ⋙ G ≅ H`, the induced functors on derived categories satisfy
`D(F) ⋙ D(G) ≅ D(H)` (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso γ`, through
`D(F ⋙ G) ≅ D(F) ⋙ D(G)`). On the image `Q K` of a complex it is the image of the levelwise
components of `γ` (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_hom_app_Q`).

Consequently, a family of such isomorphisms satisfying the cocycle condition of an associator
(that of a pseudofunctor) on the abelian categories induces one satisfying the cocycle condition
on the derived categories (`CategoryTheory.Functor.mapDerivedCategoryCompNatIso_cocycle`). This is
used to pass the associativity constraints of extensions of scalars to derived categories.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

section

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end

variable {A₁ A₂ A₃ A₄ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category A₄]
  [Abelian A₁] [Abelian A₂] [Abelian A₃] [Abelian A₄]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory A₃] [HasDerivedCategory A₄]
  {F₁₂ : A₁ ⥤ A₂} {F₂₃ : A₂ ⥤ A₃} {F₃₄ : A₃ ⥤ A₄} {F₁₃ : A₁ ⥤ A₃} {F₂₄ : A₂ ⥤ A₄}
  {F₁₄ : A₁ ⥤ A₄} [F₁₂.Additive] [F₂₃.Additive] [F₃₄.Additive] [F₁₃.Additive] [F₂₄.Additive]
  [F₁₄.Additive] [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₂₃] [PreservesFiniteColimits F₂₃]
  [PreservesFiniteLimits F₃₄] [PreservesFiniteColimits F₃₄]
  [PreservesFiniteLimits F₁₃] [PreservesFiniteColimits F₁₃]
  [PreservesFiniteLimits F₂₄] [PreservesFiniteColimits F₂₄]
  [PreservesFiniteLimits F₁₄] [PreservesFiniteColimits F₁₄]

end CategoryTheory.Functor
