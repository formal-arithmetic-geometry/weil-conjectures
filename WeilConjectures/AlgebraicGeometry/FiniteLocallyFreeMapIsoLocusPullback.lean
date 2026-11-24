/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleMapIsoLocus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkBaseChangeReflectsIso
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkIsoNeighborhood

/-! # Arbitrary base change detects the isomorphism locus

## References

* Stacks Project, Tags 00O0, 0BDP and 0098
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- If a pulled-back vector bundle map is invertible, its topological image lies in
the explicitly constructed locally invertible open `moduleMapIsoLocus φ`.
(Stacks, Tags 00O0, 05GF and 0098) -/
theorem range_subset_moduleMapIsoLocus_of_isIso_tensorPullback {W : Scheme.{u}}
    (M N : W.Modules) [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    {T : Scheme.{u}} (h : T ⟶ W) (hφ : IsIso ((tensorPullback h).map φ)) :
    Set.range h ⊆ (moduleMapIsoLocus φ : Set W) := by
  intro x hx
  obtain ⟨t, rfl⟩ := hx
  have := hφ
  obtain ⟨e, _⟩ := exists_tensorPullback_stalk_iso h t
  have hp : IsIso ((tensorPullback h ⋙
      RingedSpace.moduleStalkFunctor T.toRingedSpace t).map φ) := by
    dsimp only [Functor.comp_map]
    infer_instance
  have he := (NatIso.isIso_map_iff e φ).mp hp
  have hs := isIso_moduleStalkMap_of_isIso_extendScalars M N φ h t he
  obtain ⟨U, htU, hU⟩ :=
    exists_isIso_tensorPullback_of_isIso_moduleStalkMap M N φ (h t) hs
  exact (mem_moduleMapIsoLocus φ (h t)).2 ⟨U, hU, htU⟩

end AlgebraicGeometry.Scheme.Modules
