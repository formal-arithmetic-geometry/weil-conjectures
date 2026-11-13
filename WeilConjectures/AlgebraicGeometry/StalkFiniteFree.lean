/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite locally free sheaves have finite free stalk modules. -/
theorem stalk_isFiniteFree_of_isFiniteLocallyFree
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree] (x : X) :
    Module.Free (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M) := by
  classical
  obtain ⟨q, hq, hf⟩ :=
    SheafOfModules.IsFiniteLocallyFree.exists_localGeneratorsData (M := M)
  let := hq
  let := hf
  obtain ⟨V, f, ⟨i, ⟨g⟩⟩, hxV⟩ := q.coversTop ⊤ x trivial
  have hx : x ∈ q.X i := g.le hxV
  let := hf.isFiniteType i
  let := Fintype.ofFinite (q.generators i).I
  let e := (asIso (q.generators i).π).symm
  let E := localStalkEquiv M x (q.X i) hx e
  change Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) ∧
    Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)
  exact ⟨Module.Free.of_equiv E.symm, Module.Finite.of_surjective E.symm.toLinearMap
    E.symm.surjective⟩
end AlgebraicGeometry.Scheme.Modules
