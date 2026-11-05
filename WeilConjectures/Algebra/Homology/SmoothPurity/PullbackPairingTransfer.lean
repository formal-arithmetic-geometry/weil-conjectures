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
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSitePullback.PullbackLocalizationOfUniverses

/-!
# Transfer of pairings along a morphism of ringed sites

Source: Stacks Project, Modules on Sites, Tags 03EL, 03EO and 0GMX.
(blueprint: lem-pur-ringed-site-pullback-pairing-transfer)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

open SheafOfModules.RingedSitePullback

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Construction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  [∀ V : C, (Over.post (X := V) U).IsContinuous (J.over V) (K.over (U.obj V))]
  [(pushforward.{max u v w} a).IsRightAdjoint]
  [∀ V : C, (pushforward.{max u v w} (locMap a V)).IsRightAdjoint]
  (L P : SheafOfModules.{max u v w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (b : P ⟶ homObj L (unit _))

end Construction

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

end SheafOfModules
