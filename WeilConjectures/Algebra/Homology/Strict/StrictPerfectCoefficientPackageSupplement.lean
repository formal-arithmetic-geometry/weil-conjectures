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

/-- The degreewise idempotent associated to the chosen splitting. -/
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

/-- Termwise sheafification, including the differential. -/
noncomputable def strictPerfectConstantComplex (F : CochainComplex (ModuleCat.{u} Λ) ℤ) :=
  ((strictPerfectConstantSheaf J Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj F

/-- Transport of a degreewise splitting through sheafification and the finite-free comparison. -/
theorem strictPerfectConstant_splitting {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : ModuleCat.StrictPerfectCoefficientPackage F) (r : ℤ) :
    ((strictPerfectConstantSheaf J Λ).map (P.i r) ≫
      strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
      (inv (strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
        (strictPerfectConstantSheaf J Λ).map (P.p r)) =
      𝟙 ((strictPerfectConstantComplex J Λ F).X r) := by
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Functor.map_comp, P.splitting]
  exact (strictPerfectConstantSheaf J Λ).map_id (F.X r)

/-- The associated constant package: sheafify the complex and both splitting maps termwise,
then identify the constant finite tuples with finite tuples of the constant ring sheaf. -/
noncomputable def _root_.ModuleCat.StrictPerfectCoefficientPackage.constant
    {F : CochainComplex (ModuleCat.{u} Λ) ℤ} (P : ModuleCat.StrictPerfectCoefficientPackage F) :
    SheafOfModules.StrictPerfectCoefficientPackage _ (strictPerfectConstantComplex J Λ F) where
  N := P.N
  i r := (strictPerfectConstantSheaf J Λ).map (P.i r) ≫
    strictPerfectConstantFiniteFreeComparison J Λ (P.N r)
  p r := inv (strictPerfectConstantFiniteFreeComparison J Λ (P.N r)) ≫
    (strictPerfectConstantSheaf J Λ).map (P.p r)
  splitting := strictPerfectConstant_splitting J Λ P

/-- The idempotent identities of a sheaf coefficient package. -/
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

/-- The degreewise idempotent of a global coefficient package. -/
def StrictPerfectCoefficientPackage.e {F : CochainComplex (ModuleCat.{u} Λ) ℤ}
    (P : StrictPerfectCoefficientPackage F) (r : ℤ) := P.p r ≫ P.i r

/-- The idempotent identities of a global coefficient package. -/
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
