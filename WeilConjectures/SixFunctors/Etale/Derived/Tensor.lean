/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!

# The derived tensor product of étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme.
The category `Sheaf X.smallEtaleTopology A` of `A`-valued étale sheaves on `X` is then a
monoidal Grothendieck abelian category, so it has a derived category `D(X_ét)`, and the
K-flat machinery migrated from mathlib PR #25848 equips `D(X_ét)` with the *derived tensor
product* `- ⊗ᴸ -`, the total left derived functor of `- ⊗ -` in two variables.

## Main definitions

- `AlgebraicGeometry.Etale.derivedTensor` : the derived tensor product
  `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, with scoped notation `(X)⊗ᴸ[A]`.

## Main results

- `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor` : the derived tensor product
  really is the total left derived functor of the tensor product of étale sheaves, in two
  variables.

- `AlgebraicGeometry.Etale.laxMonoidal_Q` : the localization functor
  `Q : C(X_ét) ⥤ D(X_ét)` is lax monoidal.

## Implementation notes

The monoidal structure on `Sheaf X.smallEtaleTopology A` is `Sheaf.monoidalCategory`, which
is a `local instance` in mathlib rather than a global one (it is only available once
`(J.W).IsMonoidal` holds). It is therefore activated by `attribute [local instance]` here, as
in `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`. Note that the *type* of
`derivedTensor` does not mention the monoidal structure, so downstream files may use it
without re-activating the local instance.

That `D(X_ét)` is monoidal at all comes from
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, which is why
the hypotheses below are exactly the ones that instance asks of the category of étale
sheaves: monoidal closed (so that tensoring preserves colimits) and admitting functorial
flat resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]

variable (X : Scheme.{u})

variable [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The derived tensor product `- ⊗ᴸ - : D(X_ét) ⥤ D(X_ét) ⥤ D(X_ét)` on the unbounded
derived category of `A`-valued étale sheaves on `X`: the tensor product of the monoidal
structure on `D(X_ét)` obtained from the K-flat left derivability structure. -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")[" A "]" => derivedTensor A X

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Sheaf X.smallEtaleTopology A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQ (Sheaf X.smallEtaleTopology A)

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQh (Sheaf X.smallEtaleTopology A)

/-- This is a slow instance -/
instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)[A].IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A) (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Sheaf X.smallEtaleTopology A)

end Etale

end AlgebraicGeometry
