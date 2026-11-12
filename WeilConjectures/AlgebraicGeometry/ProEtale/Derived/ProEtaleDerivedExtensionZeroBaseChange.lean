/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories

/-!
# Ordinary pro-etale extension-by-zero base change

Source: Stacks Project, Tag 03S6 (`lemma-shriek-base-change`), and Tag 09AE;
blueprint `lem-cbc-proetale-extension-zero-base-change`.

This is the ordinary constant-coefficient interface corresponding to the dependency
node.  The previously recorded strict-tower `singleBeta` interface has a different
category, so this module exposes the canonical mate construction on ordinary
pro-etale module sheaves and its derived map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical ordinary pro-etale extension-by-zero base-change isomorphism,
from `g⁻¹ j_!` to `j'_! g_U⁻¹`, applied degreewise.  Its inverse on sheaves is the
conjugate, under `j_! ⋙ g⁻¹ ⊣ g_* ⋙ j⁻¹` and `g_U⁻¹ ⋙ j'_! ⊣ j'⁻¹ ⋙ g_{U,*}`, of the
weakly etale base-change isomorphism `ProEtale.baseChangeMap` of the chosen cartesian
square: the construction of the upstream `derivedOpenImmersionLowerShriekBaseChangeIso`
(with the node's orientation), whose module cannot be imported with the side imports.
Source: Stacks Tag 03S6 (`lemma-shriek-base-change`), and Tag 09AE
(blueprint: lem-cbc-proetale-extension-zero-base-change). -/
noncomputable def ordinaryOpenExtensionBaseChangeIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (hsq : IsPullback gU j' j g) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} Λ) gU).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j').mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((conjugateIsoEquiv
        ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g))
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) gU).comp
          (openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} Λ) j'))).symm
        (@asIso _ _ _ _ (ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq)
          (ProEtale.isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} Λ) hsq))).symm ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

end AlgebraicGeometry.ProEtale
