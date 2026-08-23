/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafCompose
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The monoidal structure on étale sheaf categories

The K-flat left derivability structure used to derive the pullback `g^*` on étale
sheaves requires the sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product interacts well with coproducts and
`ℤ`-indexed colimits, and to admit functorial flat resolutions. The files of this
folder transport each of these hypotheses from the coefficient category `A` to the
categories of `A`-valued étale sheaves, so that the derived pullback only takes
hypotheses on `A`.

This file provides the monoidal structure itself, from
`CategoryTheory.Sheaf.monoidalCategory` (sheafification of the objectwise tensor
product of presheaves), which is closed by Day's reflection theorem. Its inputs are the
sheafification (from the concreteness assumptions on `A`) and the monoidality of the
class `W` of sheafification-inverting morphisms of presheaves, which is checked on the
stalks at the geometric points of the small étale site and needs the tensor product of
`A` to commute with filtered colimits in each variable.

The remaining transports are not yet formalized; they are recorded with `sorry` in the
sibling files `Preadditive`, `TensorColimits` and `FlatResolution` of this folder, and
in `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape`.

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

/- The monoidal structure on the coefficient category, whose tensor product commutes
with filtered colimits in each variable. The latter hypothesis makes the tensor product
of presheaves interact well with the stalks at the points of the small étale site; it
holds in the intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`, where the
tensor product commutes with all colimits. -/
variable [MonoidalCategory A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]

/-- The class `Y.smallEtaleTopology.W` of morphisms of `A`-valued étale presheaves
inverted by sheafification is monoidal: this is checked on the stalks at the geometric
points of `Y`, which form a conservative family of points of the small étale site. -/
instance Etale.isMonoidal_W_smallEtaleTopology :
    (Y.smallEtaleTopology.W (A := A)).IsMonoidal := by
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty.{u} Y.smallEtaleTopology
  exact hP.isMonoidal_W A

/-- The monoidal structure on `A`-valued étale sheaves induced by a monoidal structure
on the coefficient category `A`: the sheafification of the objectwise tensor product of
presheaves. -/
noncomputable instance Etale.sheafMonoidalCategory :
    MonoidalCategory (Sheaf Y.smallEtaleTopology A) :=
  Sheaf.monoidalCategory _ _

end AlgebraicGeometry
