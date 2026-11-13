/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import WeilConjectures.AlgebraicGeometry.PicardPullbackBaseChangePrimal
import WeilConjectures.AlgebraicGeometry.PicardPullbackBaseChangeDual

/-! # Canonical base change for a pulled-back module

## References

* Stacks Project, Tags 0BDP and 01E8
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Both canonical direct-image base-change maps are invertible for a module
pulled back from the base and its dual (Stacks, Tags 0BDP, 01E8 and 08HY). -/
theorem picard_pullback_base_change {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    ∀ {T' : Scheme.{u}} (h : T' ⟶ T),
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) ∧
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition
          ((Modules.tensorPullback (pullback.fst f g)).obj (Modules.dual E))) := by
  intro T' h
  exact ⟨picard_pullback_base_change_primal f hO E g N e h,
    picard_pullback_base_change_dual f hO E g N e h⟩

end AlgebraicGeometry.Scheme
