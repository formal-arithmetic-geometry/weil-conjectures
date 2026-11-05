/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarPullbackSquare
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # Uniqueness of the normalized signed pullback comparison

Source: Stacks Project, Tags 03EL, 0GMX, 0FNY and 07A4; the current blueprint,
Powers and duals in det-prop-sfb-cartesian-coefficients-twists.
(blueprint: lem-pur-signed-line-pullback-unique)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w z

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace SheafOfModules

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {R : Sheaf J CommRingCat.{max u v w}}
  {S : Sheaf K CommRingCat.{max u v w}}

variable [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]
  (hcover : CoverPreserving J K U)
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [∀ V : D, (K.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (P : ringedSiteModules.{max u v w}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (Q : ringedSiteModules.{max u v w}
    ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
  (t : (ringedSitePullbackFunctor a
    (module_pushforward_isRightAdjoint_of_universes a)).obj P ≅ Q)

end SheafOfModules
