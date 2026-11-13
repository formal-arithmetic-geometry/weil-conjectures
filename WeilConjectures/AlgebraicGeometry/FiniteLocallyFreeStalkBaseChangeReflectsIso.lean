/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.StalkFiniteFree
import WeilConjectures.AlgebraicGeometry.LocalFreeBaseChangeReflectsIso

/-! # Reflection of invertibility at a vector bundle stalk

## References

* Stacks Project, Tag 00O0
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Extension along the local ring map of a scheme morphism reflects invertibility
of a map between finite locally free stalks. (Stacks, Tag 00O0) -/
theorem isIso_moduleStalkMap_of_isIso_extendScalars
    {W T : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    (h : T ⟶ W) (t : T)
    (hφ : IsIso ((ModuleCat.extendScalars (h.stalkMap t).hom).map
      ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ))) :
    IsIso ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ) := by
  let R := W.presheaf.stalk (h t)
  let S := T.presheaf.stalk t
  let f : R →+* S := (h.stalkMap t).hom
  have hM := stalk_isFiniteFree_of_isFiniteLocallyFree M (h t)
  have hN := stalk_isFiniteFree_of_isFiniteLocallyFree N (h t)
  have := hM.1
  have := hM.2
  have := hN.1
  have := hN.2
  exact isIso_of_isIso_extendScalars_of_finite_free f
    ((RingedSpace.moduleStalkFunctor W.toRingedSpace (h t)).map φ) hφ

end AlgebraicGeometry.Scheme.Modules
