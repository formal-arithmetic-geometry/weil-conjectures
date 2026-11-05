/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower

/-! # Strict composites in a system of restriction functors

Source: Stacks Tag 03DA; blueprint DVR effectivity, composition of strict finite models.
(blueprint: lem-coef-strict-restriction-tower-composites).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b r w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace WeilConjectures
attribute [local instance 30000] SheafOfModules.instPreadditive
  Functor.preservesZeroMorphisms_of_additive
section RestrictionComposition
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S T : Sheaf J RingCat.{r}}

end RestrictionComposition

namespace StrictRestrictionData
variable {B : ℕ → Type a} [∀ n, Category.{b} (B n)]
  {A : Type r} [Category.{w} A] (data : StrictRestrictionData B A)

variable (P : ∀ n, B n) (g : ∀ n, P (n + 1) ⟶ (data.finite n.le_succ).obj (P n))

variable [HasZeroMorphisms A] [HasZeroObject A]

end StrictRestrictionData

variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}

namespace SheafRestrictionTowerData
variable {coefficient : ℕ → Sheaf J RingCat.{r}} {completed : Sheaf J RingCat.{r}}
  (syst : SheafRestrictionTowerData.{a, b, r, w} coefficient completed)

variable (P : ∀ j : ℕ, CochainComplex (SheafOfModules.{w} (coefficient j)) ℤ)
  (g : ∀ j : ℕ, P (j + 1) ⟶
    ((SheafOfModules.restrictScalars (syst.quotient j.le_succ)).mapHomologicalComplex
      (.up ℤ)).obj (P j))

variable [HasZeroObject (SheafOfModules.{w} completed)]

end SheafRestrictionTowerData
end WeilConjectures
