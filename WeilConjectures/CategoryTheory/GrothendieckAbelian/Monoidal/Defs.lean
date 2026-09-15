/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!

# The monoidal structure on étale sheaf categories

The K-flat left derivability structure used to derive the pullback `g^*` on étale
sheaves requires the sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product preserves colimits, and to admit
functorial flat resolutions. The files of this folder supply each of these for the
categories of `A`-valued étale sheaves, so that the derived pullback only takes
hypotheses on the coefficient category `A`.

This file provides the monoidal structure itself, from
`CategoryTheory.Sheaf.monoidalCategory` (sheafification of the objectwise tensor
product of presheaves), together with its braiding
(`CategoryTheory.Sheaf.braidedCategory`). Their inputs are the sheafification (from
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`) and the monoidality of
the class `W` of sheafification-inverting morphisms of presheaves.

That monoidality is `CategoryTheory.GrothendieckTopology.W.monoidal`: for a *closed
braided* coefficient category `A`, the class `W` is stable under tensoring on either
side, because tensoring by `F` is left adjoint to the internal hom `[F, -]`, which
preserves sheaves (`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`), and the
braiding exchanges the two sides. This replaces the earlier stalkwise argument, which
required `A` to be concrete with a limit- and filtered-colimit-preserving forgetful
functor and could not be carried out with the coefficient category at `Type (u + 1)`:
mathlib's stalkwise criterion `ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`
wants a conservative family of `Point.{u + 1}`-points of the small étale site, while
mathlib only supplies `Point.{u}`-points. No concreteness hypothesis on `A` is left in
this folder.

The enriched-hom hypotheses of `GrothendieckTopology.W.monoidal` — the ends
`HasEnrichedHom A F₁ F₂` and `HasFunctorEnrichedHom A F₁ F₂` for presheaves `F₁ F₂` on
the small étale site — are not assumed: they are limits of size `u + 1`, which a
Grothendieck abelian category with `Hom`-types in `Type (u + 1)` has by
`CategoryTheory.IsGrothendieckAbelian.hasLimits`.

Mathlib deliberately does not make `Sheaf.monoidalCategory` an instance, because for a
general coefficient category it can clash with a monoidal structure coming from chosen
finite products. No such clash arises here: the coefficient categories of this
development are abelian, and `Sheaf Y.smallEtaleTopology A` carries no cartesian monoidal
structure — its finite products are biproducts, for which mathlib registers no
`MonoidalCategory` instance. The two instances of this file are therefore global.

The preadditivity of this monoidal structure needs no transport of its own: it is
`CategoryTheory.Sheaf.monoidalPreadditive` of
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`, which applies to any sheaf
category. The remaining transports are in the sibling files `TensorColimits` and
`FlatResolution` of this folder; the latter is still recorded with `sorry`.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

/- The monoidal structure on the coefficient category. It is assumed *closed* and
*braided*: closedness makes tensoring by a fixed presheaf a left adjoint whose right
adjoint preserves sheaves, hence makes the class of sheafification-inverting morphisms
stable under tensoring on the left, and the braiding transports this to the right. Both
hold, and are mathlib instances, in the intended application `A = ModuleCat.{u + 1} Λ`
with `Λ` a commutative ring — which is even symmetric monoidal closed, and covers
`A = Ab.{u + 1}` through `Λ = ℤ`. -/
variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- The monoidal structure on `A`-valued étale sheaves induced by a monoidal structure
on the coefficient category `A`: the sheafification of the objectwise tensor product of
presheaves. -/
noncomputable instance Etale.sheafMonoidalCategory :
    MonoidalCategory (Sheaf Y.smallEtaleTopology A) :=
  Sheaf.monoidalCategory _ _

/-- The braiding of the monoidal structure on `A`-valued étale sheaves, induced by the
braiding of the coefficient category `A`. -/
noncomputable instance Etale.sheafBraidedCategory :
    BraidedCategory (Sheaf Y.smallEtaleTopology A) :=
  Sheaf.braidedCategory _ _

end AlgebraicGeometry
