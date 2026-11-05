/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension

/-!
# Tensor and module sheafification in the pro-etale site universes

Source: Stacks Project, Modules on Sites, Tag 0GMW. This is the existing tensor
comparison argument with site object universe u+1 and Hom universe u.
-/

@[expose] public section

universe u

set_option maxRecDepth 500

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option autoImplicit false

end SheafOfModules

namespace PresheafOfModules

set_option autoImplicit false

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {O : Cᵒᵖ ⥤ CommRingCat.{u + 1}} {R : Sheaf J CommRingCat.{u + 1}}

section Comparison

variable (α : (O ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⟶
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

set_option hygiene false in
local notation "S" => sheafification α
set_option hygiene false in
local notation "η" => (sheafificationAdjunction α).unit
set_option hygiene false in
local notation "a" => sheafification
  (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
set_option hygiene false in
local notation "ηR" => (sheafificationAdjunction
  (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).unit

attribute [irreducible] sheafificationTensorComparisonApp

attribute [irreducible] tensorPure

end Comparison

attribute [local irreducible] SheafOfModules.monoidalCategory sheafification

end PresheafOfModules
