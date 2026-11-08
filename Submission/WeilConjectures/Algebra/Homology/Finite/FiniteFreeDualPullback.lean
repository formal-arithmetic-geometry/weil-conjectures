/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import Mathlib.CategoryTheory.Sites.LocalProperties

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Pullback of the dual of a finite locally free module on a ringed site

Source: Stacks Project, Modules on Sites, Tags 0GMX and 0FNY; the Powers and duals
paragraph of `det-prop-sfb-cartesian-coefficients-twists`, main-20261015
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback).

The coefficient morphism `a : R → u_* S` is the adjunct of the source's
`c : f⁻¹ R → S`. The module pullback is Mathlib's left adjoint, hence the same
sheafified relative tensor product. Its adjunction unit sends a section to its
pulled-back section. The equation below characterizes the canonical comparison
by evaluation on these sections, exactly as in Stacks 0GMX. In particular it
specializes to the stated Kronecker-delta formula for every local dual basis.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

set_option autoImplicit false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  {R : Sheaf J CommRingCat.{max u v w}} {S : Sheaf K CommRingCat.{max u v w}}
  (a : (sheafCompose J (forget₂ CommRingCat RingCat)).obj R ⟶
    (U.sheafPushforwardContinuous RingCat J K).obj
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))

/-- Mathlib's module pullback with its existence proof supplied explicitly.
This transparent abbreviation permits the statement to assert existence of the
adjoint instead of imposing it as a further hypothesis. Source: Stacks Project,
Modules on Sites, Tags 03D7 and 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable abbrev ringedSitePullbackFunctor
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint) :=
  @pullback _ _ _ _ _ _ _ _ _ _ a hAdj

/-- A section pulled back along a ringed site morphism, using the unit of the
module pullback adjunction. This is the image `1 ⊗ f⁻¹(m)` in the sheafified tensor
product. Source: Stacks Project, Modules on Sites, Tag 0GMX
(blueprint: lem-pur-ringed-site-finite-free-dual-pullback). -/
noncomputable def ringedSitePullbackSection
    (hAdj : (pushforward.{max u v w} a).IsRightAdjoint)
    (M : ringedSiteModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (V : C)
    (m : M.val.obj (op V)) : ((ringedSitePullbackFunctor a hAdj).obj M).val.obj (op (U.obj V)) :=
  ((@pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ a hAdj).unit.app M).val.app
    (op V) m

end SheafOfModules
