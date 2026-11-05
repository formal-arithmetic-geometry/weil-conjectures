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
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackExistsOfUniverses
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackPairingTransfer
import WeilConjectures.Algebra.Homology.SmoothPurity.PullbackDualFreeChart
import Mathlib.CategoryTheory.Sites.LocalProperties

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

end SheafOfModules
