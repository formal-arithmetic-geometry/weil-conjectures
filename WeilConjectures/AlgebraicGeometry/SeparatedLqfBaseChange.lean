/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.IsolatedFibrePointBaseChange
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Base change of separated and locally quasi-finite morphisms

## References

* [Stacks Project, Tag 01KU](https://stacks.math.columbia.edu/tag/01KU)
* [Stacks Project, Tag 01TM](https://stacks.math.columbia.edu/tag/01TM)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Separatedness and local quasi-finiteness are preserved by base change.
-/
theorem separated_lqf_base_change {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (IsSeparated f → IsSeparated (pullback.snd f g)) ∧
      (Scheme.Hom.IsLocallyQuasiFinite f →
        Scheme.Hom.IsLocallyQuasiFinite (pullback.snd f g)) := by
  constructor
  · intro hf
    have : IsSeparated f := hf
    infer_instance
  · intro hf
    have : LocallyOfFiniteType f := f.locallyOfFiniteType_of_isLocallyQuasiFinite hf
    intro x'
    have hisolated := isolated_fiber_point_base_change f g x'
      (f.quasiFiniteAtPoint_isolated_in_fiber (pullback.fst f g x')
        (hf (pullback.fst f g x'))).1
    obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show (pullback.snd f g) x' ∈ (⊤ : S'.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show x' ∈ (pullback.snd f g) ⁻¹ᵁ V from hxV)
    refine ⟨U, hxU, hU, V, hV, hUV, ?_⟩
    exact (pullback.snd f g).isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber
      x' hisolated U V hU hV hxU hUV

end AlgebraicGeometry
