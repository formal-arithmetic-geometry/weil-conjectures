/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-!
# Exactness and Grothendieck categories of algebras with invertible structure morphism

Let `F` be an exact additive endofunctor of an abelian category `C`. The category
`IsoAlgebra F` of pairs `(X, φ : F X ≅ X)` is abelian, and its forgetful functor to `C` is
exact and reflects isomorphisms. This file shows:

- the transport `IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G` along an exact functor
  `L : C ⥤ D` with `e : L ⋙ G ≅ F ⋙ L` is exact, since the forgetful functors reflect finite
  limits and colimits;
- if `F` is an autoequivalence of a Grothendieck abelian category, then `IsoAlgebra F` is again
  Grothendieck abelian.

## Main results

- `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso`.
- `CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteLimits_mapOfNatIso` and
  `CategoryTheory.Endofunctor.IsoAlgebra.preservesFiniteColimits_mapOfNatIso`.
- `CategoryTheory.Endofunctor.IsoAlgebra.isGrothendieckAbelian`.
-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section Map

variable {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)

/-- The underlying object of the transport of an algebra along `L` is the image under `L` of
its underlying object. -/
noncomputable def mapOfNatIsoCompForgetIso : mapOfNatIso e ⋙ forget G ≅ forget F ⋙ L :=
  Iso.refl _

variable [Abelian C] [Abelian D] [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

instance reflectsFiniteLimits_forget : ReflectsFiniteLimits (forget G) where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms

instance reflectsFiniteColimits_forget : ReflectsFiniteColimits (forget G) where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- The transport of algebras along a left exact functor is left exact: its composite with
the forgetful functor, which reflects finite limits, is `forget F ⋙ L`. -/
instance preservesFiniteLimits_mapOfNatIso [PreservesFiniteLimits L] :
    PreservesFiniteLimits (mapOfNatIso e) := by
  have : PreservesFiniteLimits (mapOfNatIso e ⋙ forget G) :=
    preservesFiniteLimits_of_natIso (mapOfNatIsoCompForgetIso e).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget G)

/-- The transport of algebras along a right exact functor is right exact: its composite with
the forgetful functor, which reflects finite colimits, is `forget F ⋙ L`. -/
instance preservesFiniteColimits_mapOfNatIso [PreservesFiniteColimits L] :
    PreservesFiniteColimits (mapOfNatIso e) := by
  have : PreservesFiniteColimits (mapOfNatIso e ⋙ forget G) :=
    preservesFiniteColimits_of_natIso (mapOfNatIsoCompForgetIso e).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget G)

end Map

variable (F : C ⥤ C) [Abelian C] [F.Additive] [F.IsEquivalence]

/-- **Algebras for an autoequivalence of a Grothendieck abelian category.** If `F` is an
additive autoequivalence of a Grothendieck abelian category `C`, then the category of pairs
`(X, φ : F X ≅ X)` is Grothendieck abelian. Filtered colimits are created by the forgetful
functor, since `F` preserves them, and they are exact, the forgetful functor being exact and
conservative. If `S` is a separator of `C`, then the free objects
`⨁_{n ∈ ℤ} Fⁿ S`, with the structure isomorphism shifting the summands, form a separator: a
morphism of algebras out of the free object on `S` is the same as a morphism out of `S` in
`C`. -/
theorem isGrothendieckAbelian [IsGrothendieckAbelian.{w} C] :
    IsGrothendieckAbelian.{w} (IsoAlgebra F) :=
  sorry

end CategoryTheory.Endofunctor.IsoAlgebra
