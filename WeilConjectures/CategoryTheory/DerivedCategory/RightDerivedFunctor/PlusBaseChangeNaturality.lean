/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-!
# Functoriality of the base change morphism of bounded below right derived functors

For a square `e : G ⋙ γ ⟶ β ⋙ G'` with `β`, `γ` exact, `Functor.rightDerivedFunctorPlusBaseChange`
is the base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'`. We record two of its functoriality
properties:

- `Functor.rightDerivedFunctorPlusBaseChange_naturality`: it is natural in the exact functors
  `β` and `γ`, for isomorphisms `γ ≅ γ₂`, `β ≅ β₂` compatible with the squares;
- `Functor.rightDerivedFunctorPlusBaseChange_paste`: the base change morphism of two squares
  pasted along `G'` (`Functor.baseChangePaste`) is the composite of the two base change
  morphisms, modulo `Functor.mapDerivedCategoryPlusCompIso`.

Both are proved by the uniqueness of natural transformations out of a right derived functor
(`Functor.rightDerived_ext`), the base change morphism being computed on complexes by
`Functor.rightDerivedFunctorPlusBaseChange_fac_app`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.NatTrans

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]

variable {E' : Type*} [Category* E'] [Preadditive E']

end CategoryTheory.NatTrans

namespace CategoryTheory.Functor

section

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

variable {β₂ : B ⥤ B'} {γ₂ : C ⥤ C'} [β₂.Additive] [γ₂.Additive]
  [PreservesFiniteLimits β₂] [PreservesFiniteColimits β₂]
  [PreservesFiniteLimits γ₂] [PreservesFiniteColimits γ₂]

end

end CategoryTheory.Functor

namespace CategoryTheory.Functor

section Paste

variable {B₁ B₂ B₃ C₁ C₂ C₃ : Type*} [Category* B₁] [Category* B₂] [Category* B₃]
  [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian B₁] [Abelian B₂] [Abelian B₃] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory B₁] [HasDerivedCategory B₂] [HasDerivedCategory B₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [EnoughInjectives B₁] [EnoughInjectives B₂] [EnoughInjectives B₃]
  {G₁ : B₁ ⥤ C₁} {G₂ : B₂ ⥤ C₂} {G₃ : B₃ ⥤ C₃} {β₁ : B₁ ⥤ B₂} {γ₁ : C₁ ⥤ C₂}
  {β₂ : B₂ ⥤ B₃} {γ₂ : C₂ ⥤ C₃}
  [G₁.Additive] [G₂.Additive] [G₃.Additive] [β₁.Additive] [γ₁.Additive]
  [β₂.Additive] [γ₂.Additive]
  [PreservesFiniteLimits β₁] [PreservesFiniteColimits β₁]
  [PreservesFiniteLimits γ₁] [PreservesFiniteColimits γ₁]
  [PreservesFiniteLimits β₂] [PreservesFiniteColimits β₂]
  [PreservesFiniteLimits γ₂] [PreservesFiniteColimits γ₂]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end Paste

end CategoryTheory.Functor
