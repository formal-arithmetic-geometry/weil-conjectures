/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Extension by zero on the small pro-etale site

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-def-sf-operations`, order 1471;
Stacks Project, Tags 03DI and 09AE (blueprint: def-weil-extension-by-zero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Extension by zero for the open immersion `U.hom : U.left ⟶ X`, in the localized-site
presentation of sheaves on `U.left`. The domain is modules over `A_X.over U` on `X.ProEt/U`:
`ProEt.weaklyEtale_localization` identifies this ringed site and its module sheaves with
`U.left.ProEt` and its constant coefficient modules, as stipulated in the node.

The first functor has sections `⨁ (φ : V ⟶ U), M(V ⟶ U)`. Since the open immersion is
monic, this is the unique summand when a factorization exists and zero otherwise.
Its restrictions are those of `M` into the corresponding summand; scalars act through
`A_X(V) = (A_X.over U)(V ⟶ U)`. A module morphism acts by its component on each summand.
The second functor sheafifies both these presheaves and their morphisms.

Source: Weil conjectures blueprint, order 1471; Stacks Project, Tags 03DI and 09AE
(blueprint: def-weil-extension-by-zero). -/
noncomputable def proEtaleExtensionByZero (X : Scheme.{u}) (U : X.ProEt)
    [IsOpenImmersion U.hom] (A : CommRingCat.{u + 1}) [Finite A] :
    ringedSiteModules.{u + 1}
        (((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)).over U) ⥤
      ringedSiteModules.{u + 1}
        ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)) :=
  SheafOfModules.extensionByZeroPresheaf
      ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)) U ⋙
    PresheafOfModules.sheafification (𝟙
      ((constantSheaf (ProEt.topology X) RingCat.{u + 1}).obj (RingCat.of A)).obj)

end AlgebraicGeometry.Scheme
