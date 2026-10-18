/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.StrictPerfectPackageOnSite

/-!
# Strict-perfect models with independent site and coefficient universes

Source: Stacks Project, Tag 08G5; Weil blueprint, order 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
The recorded general-site degreewise package is reused. The recorded small-site
local-perfectness and representation interfaces fix coefficients at the site-object
universe; these forms also allow independently larger coefficients.

## Main definitions

- `IsLocallyStrictPerfectComplexOfUniverses`
- `IsPerfectOnRingedSiteOfUniverses`
- `StrictPerfectCoefficientRepresentationOfUniverses`
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe uC vC r w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max uC vC r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- Locally bounded models by finite-free retracts, on covering sieves.
Bounds and ranks may depend on the member of the cover. Source: Stacks Tag 08G5
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsLocallyStrictPerfectComplexOfUniverses (R : Sheaf J CommRingCat.{max uC vC r})
    (K : CochainComplex (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)) ℤ) : Prop :=
  ∀ V : C, ∃ S : Sieve V, S ∈ J V ∧
    ∀ (U : C) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (SheafOfModules.{max uC vC r}
          (((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over U)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        Nonempty (StrictPerfectCoefficientPackageOnSite.{max uC vC, vC, max uC vC r} _ F) ∧
        ∃ α : F ⟶ ((SheafOfModules.overFunctor _ U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K, QuasiIso α

/-- Derived objects represented by locally strictly perfect complexes on a general site.
Source: Stacks Tag 08G5 (blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def IsPerfectOnRingedSiteOfUniverses (R : Sheaf J CommRingCat.{max uC vC r})
    [HasDerivedCategory.{w} (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))]
    (K : DerivedCategory (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R))) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{max uC vC r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R)) ℤ,
    IsLocallyStrictPerfectComplexOfUniverses.{uC, vC, r} R P ∧
      Nonempty (K ≅ DerivedCategory.Q.obj P)

/-- The bounded representative and its degreewise package on the localized site.
The same definition as the recorded representation, with separate site universes.
Source: Weil blueprint, order 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
structure StrictPerfectCoefficientRepresentationOfUniverses
    (R : Sheaf J CommRingCat.{max uC vC r}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{max uC vC r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over U))]
    (Q : DerivedCategory (SheafOfModules.{max uC vC r}
      (((sheafCompose J
        (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over U))) where
  /-- The cochain representative. -/
  F : CochainComplex (SheafOfModules.{max uC vC r}
    (((sheafCompose J
      (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})).obj R).over U)) ℤ
  /-- Strict boundedness of its terms. -/
  bounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)
  /-- Its specified identification with the localized derived object. -/
  represents : Q ≅ DerivedCategory.Q.obj F
  /-- The chosen finite free splittings, degree by degree. -/
  package : StrictPerfectCoefficientPackageOnSite.{max uC vC, vC, max uC vC r} _ F

end SheafOfModules
