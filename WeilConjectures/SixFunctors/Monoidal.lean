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
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
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

We moreover record the basic supply of dualizable objects of this category: the constant
sheaf of a finite free `Λ`-module `M` is dualizable, with dual the constant sheaf of the
dual module (`AlgebraicGeometry.Scheme.hasRightDual_constantSheaf_smallEtaleTopology`
and the companions below), and the monoidal stalk functors send dualizable sheaves to
dualizable modules. These are the coefficient objects for which the projection formula
of the six-functor formalism holds.

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

/-! ### Dualizable constant sheaves

The constant sheaf of a finite free `Λ`-module is a dualizable object of the symmetric
monoidal category of étale sheaves of `Λ`-modules, with dual the constant sheaf of the
dual module. These are the coefficient objects for which the projection formula of the
six-functor formalism holds. -/

variable (M : ModuleCat.{u} Λ) [Module.Free Λ M] [Module.Finite Λ M]

/-- The constant étale sheaf of a finite free `Λ`-module has a right dual, given by the
constant sheaf of the dual module. -/
noncomputable instance hasRightDual_constantSheaf_smallEtaleTopology :
    HasRightDual ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M) :=
  constantSheafObjHasRightDual X.smallEtaleTopology (ModuleCat.{u} Λ) M

/-- The constant étale sheaf of a finite free `Λ`-module has a left dual, given by the
constant sheaf of the dual module, since the category of étale sheaves of `Λ`-modules is
symmetric monoidal. -/
noncomputable instance hasLeftDual_constantSheaf_smallEtaleTopology :
    HasLeftDual ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M) :=
  constantSheafObjHasLeftDual X.smallEtaleTopology (ModuleCat.{u} Λ) M

/-- The dual of the constant étale sheaf of a finite free `Λ`-module is the constant
sheaf of the dual module (definitionally, for the chosen duals). -/
theorem rightDual_constantSheaf_smallEtaleTopology :
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj M)ᘁ =
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (ModuleCat.of Λ (Module.Dual Λ M)) :=
  rfl

-- The stalk functor at a geometric point of `X` sends a sheaf with a right dual to a
-- module with a right dual, given by the stalk of the dual.
noncomputable example {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) [HasRightDual F] :
    HasRightDual (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).obj F) :=
  HasRightDual.map _ F

-- For a dualizable sheaf whose stalk is also equipped with a dual, the stalk of the dual
-- is canonically isomorphic to the dual of the stalk.
noncomputable example {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) [HasRightDual F]
    [HasRightDual (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).obj F)] :
    ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).obj (Fᘁ) ≅
      (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).obj F)ᘁ :=
  Functor.Monoidal.mapRightDualIso _ F

end AlgebraicGeometry.Scheme
