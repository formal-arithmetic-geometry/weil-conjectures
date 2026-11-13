/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Quasi-finite morphisms are locally quasi-finite and quasi-compact

## References

* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 01TJ](https://stacks.math.columbia.edu/tag/01TJ)
-/

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is quasi-finite exactly when it is locally quasi-finite and
quasi-compact.
-/
theorem isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact
    {X S : AlgebraicGeometry.Scheme.{v}} (f : X ⟶ S) :
    IsQuasiFinite f ↔ IsLocallyQuasiFinite f ∧ AlgebraicGeometry.QuasiCompact f := by
  constructor
  · rintro ⟨hlft, hqc, hisolated⟩
    let := hlft
    refine ⟨?_, hqc⟩
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
    refine ⟨U, hxU, hU, V, hV, hUV, ?_⟩
    exact f.isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber x (hisolated x)
      U V hU hV hxU hUV
  · rintro ⟨hlqf, hqc⟩
    have hlft := locallyOfFiniteType_of_isLocallyQuasiFinite f hlqf
    let := hlft
    refine ⟨hlft, hqc, ?_⟩
    intro x
    exact (quasiFiniteAtPoint_isolated_in_fiber f x (hlqf x)).1

end AlgebraicGeometry.Scheme.Hom
