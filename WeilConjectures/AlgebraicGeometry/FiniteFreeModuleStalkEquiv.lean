/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank

/-! # Coordinate equivalence for finite free module stalks

## References

Stacks Project, Modules, Tag 01C6.
-/

@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk of a finite free module sheaf has the same finite coordinate set.
(Stacks, Tag 01C6.) -/
theorem exists_finite_free_moduleStalk_linearEquiv (X : Scheme.{u})
    (I : Type u) [Finite I] (x : X) :
    Nonempty (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.free (R := X.ringCatSheaf) I)) ≃ₗ[X.presheaf.stalk x]
        (I → X.presheaf.stalk x)) := by
  classical
  let := Fintype.ofFinite I
  let E : X.Modules := SheafOfModules.free (R := X.ringCatSheaf) I
  have : (SheafOfModules.overFunctor.{u} X.ringCatSheaf ⊤).IsLeftAdjoint := by
    dsimp [SheafOfModules.overFunctor]
    infer_instance
  let e : E.over ⊤ ≅ SheafOfModules.free (R := X.ringCatSheaf.over ⊤) I :=
    (SheafOfModules.mapFreeIso (SheafOfModules.overFunctor X.ringCatSheaf ⊤)
      I (Iso.refl _)).symm
  exact ⟨localStalkEquiv E x ⊤ (by trivial) e⟩

end AlgebraicGeometry.Scheme.Modules
