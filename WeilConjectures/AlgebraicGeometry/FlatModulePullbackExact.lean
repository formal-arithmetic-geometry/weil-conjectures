/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Flat module pullback is exact and direct image preserves injectives

## References

* Stacks Project, Tag 02N4 (Modules) and Tag 02N5 (Cohomology)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a flat morphism of schemes, module pullback is exact and pushforward preserves
injective objects (Stacks, Tags 02N4 and 02N5). -/
theorem flat_module_pullback_exact_pushforward_injective
    {X Y : Scheme.{u}} (h : X ⟶ Y) [Flat h] :
    (PreservesFiniteLimits (Scheme.Modules.tensorPullback h) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback h)) ∧
      (Scheme.Modules.pushforward h).PreservesInjectiveObjects := by
  let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction h)
  have : (Scheme.Modules.tensorPullback h).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : PreservesFiniteColimits (Scheme.Modules.tensorPullback h) := inferInstance
  have : (Scheme.Modules.tensorPullback h).Additive := adj.left_adjoint_additive
  have hex : ∀ S : ShortComplex Y.Modules,
      S.Exact → (S.map (Scheme.Modules.tensorPullback h)).Exact := by
    intro S hS
    apply ((RingedSpace.module_stalk_exact X.toRingedSpace
      ((Scheme.Modules.tensorPullback h).map S.f)).2.2.2.2
      _ _ _ _).mpr
    intro x
    have : PreservesFiniteLimits (ModuleCat.extendScalars (h.stalkMap x).hom) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        ((Flat.iff_flat_stalkMap h).mp inferInstance x)
    have : (ModuleCat.extendScalars (h.stalkMap x).hom).PreservesZeroMorphisms :=
      inferInstance
    have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace (h x)).PreservesZeroMorphisms :=
      inferInstance
    have hy := ((RingedSpace.module_stalk_exact Y.toRingedSpace S.f).2.2.2.2
      _ _ _ _).mp hS (h x)
    have : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
      inferInstance
    have : (Scheme.Modules.tensorPullback h).PreservesZeroMorphisms := inferInstance
    have : (Scheme.Modules.tensorPullback h ⋙
        RingedSpace.moduleStalkFunctor X.toRingedSpace x).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_comp _ _
    obtain ⟨e, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso h x
    exact ShortComplex.exact_of_iso (S.mapNatIso e.symm)
      (hy.map (ModuleCat.extendScalars (h.stalkMap x).hom))
  have : (Scheme.Modules.tensorPullback h).PreservesHomology :=
    Functor.preservesHomology_of_map_exact (Scheme.Modules.tensorPullback h) hex
  have : PreservesFiniteLimits (Scheme.Modules.tensorPullback h) :=
    Functor.preservesFiniteLimits_of_preservesHomology (Scheme.Modules.tensorPullback h)
  exact ⟨⟨inferInstance, inferInstance⟩,
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj⟩

end AlgebraicGeometry
