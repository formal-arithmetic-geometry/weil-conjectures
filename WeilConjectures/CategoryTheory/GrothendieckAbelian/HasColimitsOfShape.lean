/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib

/-!

# `ℤ`-indexed colimits of étale sheaves (sorried)

The K-flat left derivability structure used to derive the pullback `g^*` on étale
sheaves requires the sheaf categories to have `ℤ`-indexed coproducts and exact
`ℤ`-indexed colimits. The instances of this file transport these hypotheses from the
Grothendieck abelian coefficient category `A` to the categories of `A`-valued étale
sheaves; they hold since the sheaf categories are Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`), but the
transports are not yet formalized and are recorded with `sorry`.

## Sorried instances

- `AlgebraicGeometry.Etale.sheafHasCoproductsOfShapeInt`: existence of `ℤ`-indexed
  coproducts of étale sheaves.
- `AlgebraicGeometry.Etale.sheafHasColimitsOfShapeInt` and
  `AlgebraicGeometry.Etale.sheafHasExactColimitsOfShapeInt`: existence and exactness of
  `ℤ`-indexed colimits of étale sheaves.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

/-- Existence of `ℤ`-indexed coproducts of étale sheaves, induced by the corresponding
condition on the coefficient category. Via
`ComplexShape.hasColimitsOfShape_discrete_π_up_int`, this provides the coproducts
defining the tensor product of complexes of étale sheaves, whose indexing fibers
`(ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}` are in
bijection with `ℤ`. -/
instance Etale.sheafHasCoproductsOfShapeInt [HasColimitsOfShape (Discrete ℤ) A] :
    HasColimitsOfShape (Discrete ℤ) (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Existence of `ℤ`-indexed colimits of étale sheaves, induced by the corresponding
condition on the coefficient category. -/
instance Etale.sheafHasColimitsOfShapeInt [HasColimitsOfShape ℤ A] :
    HasColimitsOfShape ℤ (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Exactness of `ℤ`-indexed colimits of étale sheaves, induced by the corresponding
condition on the coefficient category. -/
instance Etale.sheafHasExactColimitsOfShapeInt [HasColimitsOfShape ℤ A]
    [HasExactColimitsOfShape ℤ A] :
    HasExactColimitsOfShape ℤ (Sheaf Y.smallEtaleTopology A) :=
  sorry

end AlgebraicGeometry
