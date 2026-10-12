/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.InjectiveModuleSheafHCohomology
import Sheaf.Paper.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Forgetting coefficients in higher direct images

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-sbc-higher-direct-image-forget-comparison)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- Forgetting the module structure commutes with higher direct images of a sheaf
placed in degree zero, in every integer degree.

Source: Stacks Project, Tag 03FD (cohomology of modules agrees with abelian
cohomology), and Tag 072W (higher direct images as sheafified cohomology presheaves).
(blueprint: lem-sbc-higher-direct-image-forget-comparison)

Proof: Choose a bounded-below injective resolution of F in module-valued sheaves.
The exact forgetful functor carries its augmentation to a resolution of the
underlying abelian sheaf. Its terms are acyclic for abelian direct image: by 03FD,
cohomology over each etale object vanishes in positive degrees for an injective
module sheaf, and by 072W these groups sheafify to the higher direct image. This
uses lem-weil-pbc-injective-module-sheaf-H-acyclic on the localized small etale
sites: restriction along an etale object preserves injectives, since its left
adjoint, extension by zero, is exact. Thus the same Cech argument proves acyclicity
on every etale object, not just the terminal object. The sheafified-presheaf
comparison is lem-weil-pbc-higher-direct-image-sheafified-presheaf. An acyclic
resolution computes right derived functors by lemma-weil-pbc-leray-acyclicity.
Ordinary pushforward commutes with forgetting, since both are evaluated objectwise
on the base-change functor of the small etale sites. Forgetting is exact, so it
commutes with the homology of these pushforward complexes. This gives the stated
isomorphism. In degree zero it is the ordinary pushforward comparison; in negative
degrees both objects are zero, since the resolutions start in degree zero.
No flatness of the coefficient ring over the integers is required. -/
theorem nonempty_higherDirectImage_forget_iso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (h : Y ⟶ X)
    (q : ℤ) (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          (higherDirectImage Λ h q F) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
              ((sheafCompose Y.smallEtaleTopology
                (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)))) := by sorry

end AlgebraicGeometry.Etale
