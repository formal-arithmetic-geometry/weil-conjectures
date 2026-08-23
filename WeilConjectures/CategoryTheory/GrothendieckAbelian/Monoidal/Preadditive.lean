/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs

/-!

# Preadditivity of the monoidal structure on étale sheaves (sorried)

The monoidal structure on `A`-valued étale sheaves provided by
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` is preadditive when
the one on the coefficient category is: the tensor product of sheaves is the
sheafification of the objectwise tensor product, and both sheafification and the
objectwise tensor product are additive in each variable. The transport is not yet
formalized and is recorded with `sorry`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]

/-- The monoidal structure on étale sheaves is preadditive when the one on the
coefficient category is. -/
instance Etale.sheafMonoidalPreadditive [MonoidalPreadditive A] :
    MonoidalPreadditive (Sheaf Y.smallEtaleTopology A) :=
  sorry

end AlgebraicGeometry
