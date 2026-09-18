/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!

# Functorial flat resolutions of sheaves on an essentially small site (sorried)

The K-flat left derivability structure computes the derived pullback on a K-flat
resolution, so it requires the sheaf categories to admit functorial flat resolutions
for the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`.

As in the sibling files, the statement is for an arbitrary site `C` with `Hom`-types in
the universe `u` and objects in `u + 1` which is essentially small in `u + 1`; the small
étale site is such a site, so the étale instance is obtained from the general one by
`inferInstance`.

The intended proof combines a functorial flat resolution in the coefficient category with
the site. For an object `U` of `C` write `j_{U!}` for the extension by zero along the
localization of the site at `U`; it is exact, left adjoint to the restriction `(-)|_U`,
and satisfies `j_{U!} P ⊗ G ≅ j_{U!} (P ⊗ G|_U)`, so `j_{U!} P` is a flat sheaf as soon as
`P` is a flat object of `A`. Applying `j_{U!}` to a functorial flat cover of the sections
`F(U)` and summing over the (essentially small) site gives a functorial epimorphism from a
flat sheaf onto `F`; it is an epimorphism because `Hom (j_{U!} P, F) ≅ Hom (P, F(U))` and a
Grothendieck abelian `A` has a separator, so the sheaves `j_{U!} P` form a generating
family. Iterating gives a functorial flat resolution. On the small étale site with
`A = ModuleCat.{u + 1} Λ` this is the construction by local free covers `⊕ j_{U!} Λ_U` of
the Stacks Project, Tag 06YL.

The construction is not yet formalized and the instance is recorded with `sorry`.

## Sorried instances

- `CategoryTheory.GrothendieckTopology.hasFunctorialFlatResolution_sheaf_essentiallySmall`:
  the category of `A`-valued sheaves on an essentially small site admits functorial flat
  resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- Functorial flat resolutions of `A`-valued sheaves on an essentially small site,
obtained by applying extension by zero to a functorial flat resolution of the sections;
see the module docstring. -/
instance hasFunctorialFlatResolution_sheaf_essentiallySmall
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf J A) :=
  sorry

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- Functorial flat resolutions of `A`-valued étale sheaves: the instance above applied to
the essentially small small étale site. -/
instance Etale.hasFunctorialFlatResolution_sheaf [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

end AlgebraicGeometry
