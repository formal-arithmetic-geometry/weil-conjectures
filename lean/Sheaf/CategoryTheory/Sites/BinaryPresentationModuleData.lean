/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
public import Sheaf.CategoryTheory.RingedPresentationData
public import Sheaf.CategoryTheory.SheafSubcategoryComparison
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Module and adjunction data for simultaneous site presentations -/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- The exact module equivalence induced by a specified ringed equivalence, together with
its termwise induced ordinary derived equivalence. The underlying-set and rank-one equations
fix the scalar action; the inverse is the specified module direct image.
Source: Stacks 03CR, 03D7 and 05RU
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationModules
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (g : RingedToposMorphism (localCoefficientRings S) (localCoefficientRings R)) where
  modules : PresentationModules R ≌ PresentationModules S
  additive : modules.functor.Additive
  inverseAdditive : modules.inverse.Additive
  finiteLimits : PreservesFiniteLimits modules.functor
  finiteColimits : PreservesFiniteColimits modules.functor
  inverseFiniteLimits : PreservesFiniteLimits modules.inverse
  inverseFiniteColimits : PreservesFiniteColimits modules.inverse
  underlying : modules.functor ⋙ presentationForget S ≅ presentationForget R ⋙ g.inverse
  unit : modules.functor.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
    SheafOfModules.unit (localCoefficientRings S)
  structural : (presentationForget S).map unit.hom =
    underlying.hom.app (SheafOfModules.unit (localCoefficientRings R)) ≫ g.ringMap
  pushforward : modules.inverse ≅ g.modules
  derived : PresentationDerived R ≌ PresentationDerived S
  derivedFunctor : derived.functor =
    presentationDerivedMap modules.functor additive finiteLimits finiteColimits
  derivedInverse : derived.inverse = presentationDerivedMap modules.inverse inverseAdditive
    inverseFiniteLimits inverseFiniteColimits

/-- A restriction square preserves both adjunctions by their actual mates. Invertibility of
these mates says precisely that the adjoints are identified compatibly with units and counits,
rather than merely giving isomorphic endpoints.
Source: Stacks Categories, Tag 0B65; Sites, Tag 03EH
(blueprint: lem-sp-binary-cover-site-presentation). -/
structure BinaryPresentationAdjointSquare
    {A B A' B' : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} A'] [Category.{u} B']
    (E : A ≌ A') (E' : B ≌ B') (F : A ⥤ B) (F' : A' ⥤ B') where
  comparison : F ⋙ E'.functor ≅ E.functor ⋙ F'
  rightMate : ∀ (G : B ⥤ A) (G' : B' ⥤ A') (a : F ⊣ G) (a' : F' ⊣ G'),
    IsIso ((mateEquiv a a' (TwoSquare.mk _ _ _ _ comparison.inv)).natTrans)
  leftMate : ∀ (L : B ⥤ A) (L' : B' ⥤ A') (a : L ⊣ F) (a' : L' ⊣ F'),
    IsIso (((mateEquiv a a').symm (TwoSquare.mk _ _ _ _ comparison.hom)).natTrans)

end CategoryTheory
