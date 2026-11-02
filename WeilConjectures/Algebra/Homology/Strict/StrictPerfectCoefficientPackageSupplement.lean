/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackage

/-!
# Strict-perfect coefficient packages

Source: the Weil conjectures blueprint, proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).

## Main definitions

- `SheafOfModules.StrictPerfectCoefficientPackage`: the chosen degreewise splittings.
- `SheafOfModules.StrictPerfectCoefficientRepresentation`: a bounded localized model.
- `SheafOfModules.IsLocallyStrictPerfectComplex` and `SheafOfModules.IsPerfectOnRingedSite`:
  local perfectness of complexes and perfectness of derived objects.
- `ModuleCat.StrictPerfectCoefficientPackage`: the global ring-module version.
- `ModuleCat.StrictPerfectCoefficientPackage.constant`: its associated constant sheaf package.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- The degreewise idempotent associated to the chosen splitting.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
noncomputable def StrictPerfectCoefficientPackage.e {R : Sheaf J RingCat.{u}}
    {F : CochainComplex (SheafOfModules.{u} R) ℤ}
    (P : StrictPerfectCoefficientPackage R F) (r : ℤ) := P.p r ≫ P.i r

attribute [instance] CategoryTheory.module_overFunctor_preservesZero

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

end ModuleCat

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

attribute [instance] strictPerfectConstantPresheaf_additive

attribute [instance] strictPerfectConstantSheaf_additive

end SheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

attribute [instance] strictPerfectConstantFiniteFreeComparison_isIso

/-- The idempotent identities of a sheaf coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: reassociate each composite and substitute `i_r ≫ p_r = 1`. The three results
are respectively `p_r ≫ i_r`, `p_r` and `i_r`. -/
theorem StrictPerfectCoefficientPackage.identities {R : Sheaf J RingCat.{u}}
    {F : CochainComplex (SheafOfModules.{u} R) ℤ}
    (P : StrictPerfectCoefficientPackage R F) (r : ℤ) :
    P.e r ≫ P.e r = P.e r ∧ P.e r ≫ P.p r = P.p r ∧ P.i r ≫ P.e r = P.i r := by
  dsimp [StrictPerfectCoefficientPackage.e]
  constructor
  · simp only [Category.assoc, ← Category.assoc (P.i r), P.splitting,
      Category.id_comp]
  constructor
  · rw [Category.assoc, P.splitting, Category.comp_id]
  · rw [← Category.assoc, P.splitting, Category.id_comp]

end SheafOfModules

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ]

/-- The degreewise idempotent of a global coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package). -/
def StrictPerfectCoefficientPackage.e {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : StrictPerfectCoefficientPackage F) (r : ℤ) := P.p r ≫ P.i r

/-- The idempotent identities of a global coefficient package.
Source: proper base change, definition 1263
(blueprint: def-weil-pbc-strict-perfect-coefficient-package).
Proof: reassociate each composite, replace the middle `i_r ≫ p_r` by the identity,
and remove the identity. -/
theorem StrictPerfectCoefficientPackage.identities {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : StrictPerfectCoefficientPackage F) (r : ℤ) :
    P.e r ≫ P.e r = P.e r ∧ P.e r ≫ P.p r = P.p r ∧ P.i r ≫ P.e r = P.i r := by
  dsimp [StrictPerfectCoefficientPackage.e]
  constructor
  · simp only [Category.assoc, ← Category.assoc (P.i r), P.splitting,
      Category.id_comp]
  constructor
  · rw [Category.assoc, P.splitting, Category.comp_id]
  · rw [← Category.assoc, P.splitting, Category.id_comp]

end ModuleCat
