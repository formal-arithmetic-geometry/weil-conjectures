/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf

/-!

# Countable coproducts of étale sheaves

The K-flat left derivability structure used to derive the pullback `g^*` on étale sheaves
computes the tensor product of complexes as a coproduct over the fibers of the total
degree map `(p, q) ↦ p + q` on `ℤ × ℤ`. These fibers are countable, so the hypothesis it
needs on the sheaf categories is `CategoryTheory.Limits.HasCountableCoproducts`.

That instance is mathlib's `CategoryTheory.Sheaf.instHasColimitsOfShape` (colimits of
sheaves are computed by sheafifying the colimit of the underlying presheaves), applied
once per countable shape. It is restated here because instance search does not find it
on its own for the small étale site: unifying a `Discrete` shape against the many
`HasColimitsOfShape` instances available for `Sheaf Y.smallEtaleTopology A` diverges,
whereas naming `Sheaf.instHasColimitsOfShape` discharges the goal instantly.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

/-- Countable coproducts of `A`-valued étale sheaves, computed by sheafifying the
coproduct of the underlying presheaves. This is mathlib's
`CategoryTheory.Sheaf.instHasColimitsOfShape`; see the module docstring for why it has to
be restated here. -/
instance (priority := high) Etale.hasCountableCoproducts_sheaf :
    HasCountableCoproducts (Sheaf Y.smallEtaleTopology A) :=
  ⟨fun _ ↦ Sheaf.instHasColimitsOfShape⟩

end AlgebraicGeometry
