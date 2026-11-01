/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Composition of the tensor comparison for extension by zero

Source: Stacks Project, Tags 0GL1 and 0E8I.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u u'

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem inverse_congr
    {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} [IsIso f] [IsIso g]
    (h : f = g) : inv f = inv g := by
  subst g
  rfl

namespace AlgebraicGeometry.Etale

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
  [MonoidalCategory B] [MonoidalPreadditive B] [SymmetricCategory B]
  [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ (Z : Scheme.{u}), Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
omit [HasSmallSiteSheafify B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B] in
section

attribute [local irreducible] Functor.mapDerivedCategory

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
end

section

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  leftDerivedUpperStarTensorComparison

omit [HasSmallSiteSheafify B] [UpperStarPreservesFlat B] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] in
end

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor

omit [HasSmallSiteSheafify B] in
end AlgebraicGeometry.Etale
