/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
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

## The reduction to a flat separator

The file is organized around the criterion
`CategoryTheory.Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator`: a
Grothendieck abelian category with a preadditive, braided, closed monoidal structure
admits functorial flat resolutions if and only if it has a *flat separator*. The
implication that matters here is the backward one: from a flat separator `G` one builds
the functorial flat cover of `F` as the coproduct `⨿_{g : G ⟶ F} G`, which is flat
because flat objects are stable under coproducts in a Grothendieck abelian category and
is an epimorphism because `G` is a separator; iterating gives a functorial flat
resolution. The forward implication reads off a flat separator from a functorial flat
resolution of an arbitrary separator.

With that criterion in hand, the sheaf statement reduces to the transfer of flat
separators along the site, `exists_flat_separator_sheaf_essentiallySmall`. The intended
proof of the latter combines a flat separator of the coefficient category with the site.
For an object `U` of `C` write `j_{U!}` for the extension by zero along the localization
of the site at `U`; it is exact, left adjoint to the restriction `(-)|_U`, and satisfies
`j_{U!} P ⊗ G ≅ j_{U!} (P ⊗ G|_U)`, so `j_{U!} P` is a flat sheaf as soon as `P` is a flat
object of `A`. Since `Hom (j_{U!} P, F) ≅ Hom (P, F(U))`, the sheaves `j_{U!} G` for `G` a
separator of `A` and `U` ranging over the (essentially small) site form a generating
family, and their coproduct is a flat separator of `Sheaf J A`. On the small étale site
with `A = ModuleCat.{u + 1} Λ` this is the construction by local free covers
`⊕ j_{U!} Λ_U` of the Stacks Project, Tag 06YL.

Neither step is formalized yet: both are recorded with `sorry`.

On the coefficient side the criterion is already enough: the free module of rank one is a
flat separator of `ModuleCat.{u} Λ`, so `ModuleCat.hasFunctorialFlatResolution` — the
only unsorried result of this file — supplies the functorial flat resolutions that the
étale six-functor files ask of their coefficient category.

## Main results

- `ModuleCat.hasFunctorialFlatResolution`: `ModuleCat.{u} Λ` admits functorial flat
  resolutions, over a commutative ring `Λ : Type u`.

## Sorried results

- `CategoryTheory.Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator`:
  functorial flat resolutions exist exactly when there is a flat separator.
- `CategoryTheory.GrothendieckTopology.exists_flat_separator_sheaf_essentiallySmall`:
  a flat separator of the coefficient category induces one of the sheaf category.

## Sorried instances

- `CategoryTheory.GrothendieckTopology.hasFunctorialFlatResolution_sheaf_essentiallySmall`:
  the category of `A`-valued sheaves on an essentially small site admits functorial flat
  resolutions. It is no longer sorried directly: it is deduced from the two results above.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace CategoryTheory.Abelian

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]

/-- A Grothendieck abelian category with a preadditive, braided, closed monoidal structure
admits functorial flat resolutions if and only if it has a flat separator; see the module
docstring. -/
theorem hasFunctorialFlatResolution_iff_exists_flat_separator :
    Abelian.HasFunctorialFlatResolution A ↔
      ∃ G : A, IsSeparator G ∧ ObjectProperty.flat G := by
  sorry

end CategoryTheory.Abelian

namespace ModuleCat

instance hasFunctorialFlatResolution (Λ : Type u) [CommRing Λ] :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} Λ) :=
  (Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator _).mpr
    ⟨ModuleCat.of Λ (Shrink.{u} Λ), ModuleCat.isSeparator.{u, u} Λ,
      ObjectProperty.prop_of_iso _
        (Shrink.linearEquiv.{u, u, u} Λ Λ).toModuleIso.symm
        (ObjectProperty.prop_unit _)⟩

end ModuleCat

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/- The monoidal structure on the coefficient category, as in the sibling file
`TensorColimits`: preadditive, symmetric and closed. The symmetry and closedness are what
make `Sheaf J A` itself monoidal closed, which is one of the hypotheses of
`Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator` below. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- A flat separator of the coefficient category `A` induces a flat separator of the
category of `A`-valued sheaves on an essentially small site, obtained by applying
extension by zero to it and summing over the site; see the module docstring. -/
theorem exists_flat_separator_sheaf_essentiallySmall
    (hA : ∃ G : A, IsSeparator G ∧ ObjectProperty.flat G) :
    ∃ G : Sheaf J A, IsSeparator G ∧ ObjectProperty.flat G :=
  sorry

/-- Functorial flat resolutions of `A`-valued sheaves on an essentially small site: by
`Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator` this is the existence of a
flat separator of `Sheaf J A`, which `exists_flat_separator_sheaf_essentiallySmall`
produces from a flat separator of `A`. -/
instance hasFunctorialFlatResolution_sheaf_essentiallySmall
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf J A) :=
  (Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator _).2
    (exists_flat_separator_sheaf_essentiallySmall A J
      ((Abelian.hasFunctorialFlatResolution_iff_exists_flat_separator A).1 ‹_›))

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]

/-- Functorial flat resolutions of `A`-valued étale sheaves: the instance above applied to
the essentially small small étale site. -/
instance Etale.hasFunctorialFlatResolution_sheaf [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  inferInstance

end AlgebraicGeometry
