/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

import WeilConjectures.AlgebraicGeometry.FormalCompletionPushforwardLimitAppBijective
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The proper pushforward comparison is invertible on inverse limits

## References

* Stacks Project, Tags 02OC and 088B
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The supplied canonical comparison induces an isomorphism of limit sheaves
(Stacks, Tags 02OC and 088B). -/
theorem formalCompletion_pushforward_limit_isIso {X Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (F : CoherentModules X)
    (h : RingedSpace.IsCoherent Y.toRingedSpace
      ((Scheme.Modules.pushforward f).obj F.obj))
    (κ : formalCompletionSystem J ((Scheme.Modules.pushforward f).obj F.obj) ⟶
      formalCompletionSystem (J.comap f) F.obj ⋙ Scheme.Modules.pushforward f)
    (hκ : ∀ n : ℕ,
      formalModuleQuotientπ J (n + 1) ((Scheme.Modules.pushforward f).obj F.obj) ≫
        κ.app (op n) = (Scheme.Modules.pushforward f).map
          (formalModuleQuotientπ (J.comap f) (n + 1) F.obj)) :
    IsIso (lim.map κ) := by
  apply Scheme.Modules.isIso_of_bijective_app_of_isAffineOpen (lim.map κ)
  intro U hU
  exact formalCompletion_pushforward_limit_app_bijective J f F h κ hκ U hU

end AlgebraicGeometry
