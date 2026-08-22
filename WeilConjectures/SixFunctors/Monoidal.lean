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
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
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
  via `CategoryTheory.Sheaf.monoidalCategory` / `Sheaf.symmetricCategory`;
- `AlgebraicGeometry.Scheme.monoidalClosed_sheaf_smallEtaleTopology`: this symmetric
  monoidal structure is closed, i.e. étale sheaves of `Λ`-modules have internal Homs.
  Day's reflection theorem does not apply to the (large) small étale site directly;
  monoidal closedness is established on the `u`-small small model of the affine étale
  site and transported up along two dense-subsite restrictions.
- `AlgebraicGeometry.Scheme.ΓIhomEquivSheafHom_sheaf_smallEtaleTopology`: the elements
  of the `Λ`-module of global sections of the internal hom `[F, G]` are the morphisms
  of sheaves `F ⟶ G`; the small étale site has a terminal object, so étale sheaves of
  `Λ`-modules admit a global sections functor.

Once these instances are available, mathlib's instances make the sheafification functor
`presheafToSheaf` and the stalk functors `(Scheme.pointSmallEtale s).sheafFiber` at
geometric points of `X` monoidal functors; this is recorded in the `example`s at the
end of this file.

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
### Monoidal closedness

The tensor structure on étale sheaves of `Λ`-modules is closed. Day's reflection theorem
(`CategoryTheory.Sheaf.monoidalClosed`) does not apply to the small étale site directly:
`X.Etale` is a large category (it is provably not essentially small), so the enriched-hom
limits the theorem requires do not exist in `ModuleCat.{u} Λ`. Instead we descend twice:
the affine étale site `X.AffineEtale` is a dense subsite with an equivalent sheaf
category, and being essentially small it in turn admits a dense subsite which is an
honest `u`-small category, its small model. Over the small model the enriched-hom limits
exist and Day's reflection theorem applies; monoidal closedness then transports back up
along the two dense-subsite restrictions
(`CategoryTheory.Functor.IsDenseSubsite.monoidalClosed`).
-/

section MonoidalClosed

open Enriched.FunctorCategory MonoidalClosed MonoidalClosed.FunctorCategory

attribute [local instance] Sheaf.monoidalCategory

/-- The local isomorphisms of presheaves of `Λ`-modules on the small model of the affine
étale site are stable under tensor product: the small model is an honest `u`-small
category, so this is mathlib's instance `CategoryTheory.GrothendieckTopology.W.monoidal`.
Instance search does not find it on its own (it gets stuck unfolding the
`HasEnoughPoints`-based instance of `Mathlib.CategoryTheory.Sites.Point.IsMonoidalW`
on a universe metavariable, as in `isMonoidal_W_smallEtaleTopology` above), so we apply
the instance by hand and record the result. -/
instance isMonoidal_W_smallModel_affineEtale :
    (((equivSmallModel.{u} X.AffineEtale).inverse.inducedTopology
      (AffineEtale.topology X)).W (A := ModuleCat.{u} Λ)).IsMonoidal :=
  GrothendieckTopology.W.monoidal

/-- The local isomorphisms of presheaves of `Λ`-modules on the affine étale site are
stable under tensor product. This is obtained by transport from the small model of the
affine étale site — where it is instance-automatic, the site being a `u`-small
category — along the dense-subsite inclusion given by the small-model equivalence. -/
instance isMonoidal_W_affineEtaleTopology :
    ((AffineEtale.topology X).W (A := ModuleCat.{u} Λ)).IsMonoidal :=
  Functor.IsDenseSubsite.isMonoidal_W (equivSmallModel.{u} X.AffineEtale).inverse
    ((equivSmallModel.{u} X.AffineEtale).inverse.inducedTopology (AffineEtale.topology X))
    (AffineEtale.topology X) (ModuleCat.{u} Λ)

/-- Sheaves of `Λ`-modules on the affine étale site of a scheme form a monoidal closed
category: Day's reflection theorem applies over the small model of the site, and
monoidal closedness transports along the small-model equivalence. -/
@[implicit_reducible]
noncomputable def monoidalClosed_sheaf_affineEtaleTopology :
    MonoidalClosed (Sheaf (AffineEtale.topology X) (ModuleCat.{u} Λ)) :=
  letI := Sheaf.monoidalClosed
    ((equivSmallModel.{u} X.AffineEtale).inverse.inducedTopology (AffineEtale.topology X))
    (ModuleCat.{u} Λ)
  Functor.IsDenseSubsite.monoidalClosed (equivSmallModel.{u} X.AffineEtale).inverse
    ((equivSmallModel.{u} X.AffineEtale).inverse.inducedTopology (AffineEtale.topology X))
    (AffineEtale.topology X) (ModuleCat.{u} Λ)

end MonoidalClosed

/-- The symmetric monoidal category of sheaves of `Λ`-modules on the small étale site
of a scheme is closed: internal Homs of étale sheaves of `Λ`-modules exist. Monoidal
closedness is transported from the affine étale dense subsite
(`AlgebraicGeometry.Scheme.monoidalClosed_sheaf_affineEtaleTopology`). -/
noncomputable instance monoidalClosed_sheaf_smallEtaleTopology :
    MonoidalClosed (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  letI := monoidalClosed_sheaf_affineEtaleTopology X Λ
  Functor.IsDenseSubsite.monoidalClosed (AffineEtale.Spec X) (AffineEtale.topology X)
    X.smallEtaleTopology (ModuleCat.{u} Λ)

/-! ### Global sections of the internal hom compute sheaf homs

The small étale site has a terminal object (the scheme itself), so étale sheaves of
`Λ`-modules admit a global sections functor; this is found by instance search. The
`Λ`-module of global sections of the internal hom `[F, G]` then computes the morphisms
of sheaves `F ⟶ G`, elementwise. -/

-- Étale sheaves of `Λ`-modules admit a global sections functor: the small étale site
-- has a terminal object.
example : HasGlobalSectionsFunctor X.smallEtaleTopology (ModuleCat.{u} Λ) :=
  inferInstance

/-- The elements of the `Λ`-module of global sections of the internal hom `[F, G]` of
étale sheaves of `Λ`-modules are the morphisms of sheaves `F ⟶ G`. This identifies
mapping into an étale sheaf `G` with taking sections of the corresponding internal hom
sheaf. -/
noncomputable def ΓIhomEquivSheafHom_sheaf_smallEtaleTopology
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u} Λ)).obj ((ihom F).obj G) : Type u) ≃
      (F ⟶ G) :=
  (ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf Λ Λ _)).toEquiv.symm.trans
    (Sheaf.unitHomΓIhomEquiv X.smallEtaleTopology (ModuleCat.{u} Λ) F G)

end AlgebraicGeometry.Scheme
