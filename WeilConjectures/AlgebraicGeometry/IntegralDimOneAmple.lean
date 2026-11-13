/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ExistsAmpleOfEnoughGloballyGenerated
import WeilConjectures.AlgebraicGeometry.FindGloballyGenerated

/-! # Ample invertible modules on integral curves

## References

* Stacks Project, Varieties, Lemma 09ND.
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- An integral Noetherian separated curve has an ample invertible module.
(Stacks, Tag 09ND) -/
theorem exists_isAmple_of_integral_dim_one
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    [Y.IsSeparated]
    (hY : topologicalKrullDim Y = (1 : WithBot ℕ∞)) :
    ∃ L : Y.Modules, ∃ hL : L.IsInvertible, @IsAmple Y L hL := by
  apply exists_isAmple_of_enough_globallyGenerated Y
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) (by simp)
  have hne : (U : Set Y).Nonempty := ⟨x, hxU⟩
  have : IsNoetherian Y := IsNoetherian.mk
  have hfin := U.isOpen.finite_compl_of_topologicalKrullDim_le_one hY.le hne
  obtain ⟨L, hL, hgen, s, hs⟩ :=
    exists_globallyGenerated_invertible_nonvanishing_eq Y hY U hU hne hfin
  exact ⟨L, hL, hgen, s, U, hs.symm, hxU, hU⟩

end AlgebraicGeometry.Scheme.Modules
