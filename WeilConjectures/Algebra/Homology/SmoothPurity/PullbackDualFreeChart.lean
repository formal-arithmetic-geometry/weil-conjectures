/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomOver
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Finite-free chart calculation for the pulled dual

Source: Stacks Project, Modules on Sites, Tags 03EL, 03EO and 0GMX.
(blueprint: lem-pur-ringed-site-pullback-dual-free-chart)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{max u v w}}
  (N : PresheafOfModules.{max u v w} (R ⋙ forget₂ _ _))

end PresheafOfModules

namespace SheafOfModules

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

section UnitHelpers

end UnitHelpers

set_option backward.isDefEq.respectTransparency true

section GlobalComparison

open SheafOfModules.RingedSitePullback
variable [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  [(pushforward.{max u v w} a).IsRightAdjoint]
  (hcover : CoverPreserving J K U)
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

end GlobalComparison

end SheafOfModules
