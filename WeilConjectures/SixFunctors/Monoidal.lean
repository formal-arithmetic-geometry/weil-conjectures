/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The symmetric monoidal category of étale sheaves of `Λ`-modules

Let `X` be a scheme and `Λ` a commutative ring. In this file we make the symmetric
monoidal category structure on `Sheaf X.smallEtaleTopology (ModuleCat Λ)` — the tensor
structure of the category `𝖠_τ(X, Λ)` of the blueprint — available as global instances:

- `AlgebraicGeometry.Scheme.isMonoidal_W_smallEtaleTopology`: the class
  `X.smallEtaleTopology.W` of local isomorphisms of presheaves of `Λ`-modules is stable
  under tensor product;
- `AlgebraicGeometry.Scheme.monoidalCategory_sheaf_smallEtaleTopology` and
  `AlgebraicGeometry.Scheme.symmetricCategory_sheaf_smallEtaleTopology`: the (symmetric)
  monoidal category structure on `Sheaf X.smallEtaleTopology (ModuleCat Λ)` obtained by
  monoidal localization of the objectwise tensor product of presheaves,
  via `CategoryTheory.Sheaf.monoidalCategory` / `Sheaf.symmetricCategory`.

Once these instances are available, mathlib's instances make the sheafification functor
`presheafToSheaf` and the stalk functors `(Scheme.pointSmallEtale s).sheafFiber` at
geometric points of `X` monoidal functors; this is recorded in the `example`s at the
end of this file.

Moreover, this monoidal structure is preadditive and `Λ`-linear: the site-level
instances `CategoryTheory.Sheaf.monoidalPreadditive` and
`CategoryTheory.Sheaf.monoidalLinear` (from
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`, imported here to make them
available at the étale level) apply to it, so that
`MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat Λ))` and
`MonoidalLinear Λ (Sheaf X.smallEtaleTopology (ModuleCat Λ))` hold by instance search;
this is also recorded in the `example`s at the end of this file.

## Implementation notes

- The small étale site `X.Etale` is a large category (it is provably not essentially
  small, see `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.NotEssentiallySmall`), so
  the generic instance `CategoryTheory.Presheaf.monoidal` of
  `Mathlib.CategoryTheory.Sites.Monoidal`, which requires enriched-hom instances for all
  presheaves, is not available. Instead we use that the geometric points of `X` form a
  conservative family of points of the small étale site
  (`AlgebraicGeometry.Scheme.isConservativeFamilyOfPoints_pointSmallEtale'`), which
  makes `X.smallEtaleTopology.W` monoidal by
  `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W`, the key
  hypothesis of `CategoryTheory.Sheaf.monoidalCategory`. Mathlib's corresponding
  instance (in `Mathlib.CategoryTheory.Sites.Point.IsMonoidalW`) is not found by
  instance search here because the universe of the family of points cannot be inferred;
  we pin it by hand.
- This route needs the forget functor of `ModuleCat Λ` to interact well with the large
  site: sheaves of `Λ`-modules must have underlying sheaves of sets
  (`HasSheafCompose`), which reduces to the forget functor preserving limits indexed by
  arbitrarily large categories. This holds because the forget functor is corepresented
  by `Λ` (`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic`). It also needs
  the tensor product of `Λ`-modules to commute with filtered colimits in both
  variables, which holds since `ModuleCat Λ` is monoidal closed and braided
  (`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided` for `tensorRight`).
- Mathlib deliberately does not make `Sheaf.monoidalCategory` an instance, since for a
  general coefficient category it can compete with other monoidal structures. For étale
  sheaves of `Λ`-modules the localized tensor product is the tensor structure of the
  six-functor formalism used throughout this development, so we register it as a global
  instance.
- The universe of `Λ` must agree with the universe of `X`, as mathlib's monoidal
  structure on `ModuleCat.{u} Λ` requires `Λ : Type u`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type u) [CommRing Λ]

/-- The local isomorphisms of presheaves of `Λ`-modules on the small étale site are
stable under tensor product, because the geometric points form a conservative family of
points. This is mathlib's instance of
`CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.isMonoidal_W` with the
universe of the family of points pinned to `u`. -/
instance isMonoidal_W_smallEtaleTopology :
    (X.smallEtaleTopology.W (A := ModuleCat.{u} Λ)).IsMonoidal :=
  (isConservativeFamilyOfPoints_pointSmallEtale' X).isMonoidal_W _

/-- The monoidal category structure on sheaves of `Λ`-modules on the small étale site
of a scheme, obtained by monoidal localization of the objectwise tensor product of
presheaves of `Λ`-modules. -/
noncomputable instance monoidalCategory_sheaf_smallEtaleTopology :
    MonoidalCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Sheaf.monoidalCategory _ _

/-- The monoidal category structure on sheaves of `Λ`-modules on the small étale site
of a scheme is symmetric. -/
noncomputable instance symmetricCategory_sheaf_smallEtaleTopology :
    SymmetricCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  Sheaf.symmetricCategory _ _

-- Sheafification of presheaves of `Λ`-modules on the small étale site is monoidal.
noncomputable example :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).Monoidal :=
  inferInstance

-- The stalk functor at a geometric point of `X` is monoidal.
noncomputable example {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X) :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).Monoidal :=
  inferInstance

/-!
### Preadditivity and `Λ`-linearity of the tensor product

The monoidal structure on étale sheaves of `Λ`-modules is preadditive and `Λ`-linear.
These facts are found by instance search once the site-level instances
`CategoryTheory.Sheaf.monoidalPreadditive` and `CategoryTheory.Sheaf.monoidalLinear` of
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` are imported: the monoidal
structure `monoidalCategory_sheaf_smallEtaleTopology` is `Sheaf.monoidalCategory`, so
the site-level instances apply to it, and `Λ`-linearity of the sheaf category itself
holds since sheaves form a full subcategory of presheaves. We record these facts as
`example`s.
-/

-- The tensor product of étale sheaves of `Λ`-modules is additive in each variable.
noncomputable example : MonoidalPreadditive (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstance

-- The category of étale sheaves of `Λ`-modules is `Λ`-linear.
noncomputable example : Linear Λ (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstance

-- The tensor product of étale sheaves of `Λ`-modules is `Λ`-linear in each variable.
noncomputable example : MonoidalLinear Λ (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstance

end AlgebraicGeometry.Scheme
