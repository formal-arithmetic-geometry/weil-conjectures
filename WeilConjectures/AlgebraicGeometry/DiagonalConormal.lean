/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Conormal module of the diagonal

## References

* Stacks Project, Tags 01R2, 01KJ and 08S2
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The conormal module of the diagonal of any scheme morphism (Stacks, Tags 01R2 and 08S2). -/
noncomputable def diagonalConormal (f : X ⟶ S) : X.Modules :=
  (Scheme.Modules.tensorPullback (pullback.diagonal f)).obj
    (kernel (SheafOfModules.unitToPushforwardObjUnit
      (pullback.diagonal f).toRingCatSheafHom))

end AlgebraicGeometry
