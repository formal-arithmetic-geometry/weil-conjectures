/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Compactification.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Valuation probes at closure points of a quasi-compact immersion

## References

* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every point in the closure of the image of a quasi-compact immersion is the centre
of a valuative commutative square. The square carries a valuation ring `sq.R`, its
fraction field `sq.K`, a map `sq.i₂ : Spec sq.R ⟶ S`, and a map `sq.i₁ : Spec sq.K ⟶ Z`.
Its commutativity says that the generic restriction of `sq.i₂` equals `sq.i₁ ≫ j`. -/
theorem exists_valuativeCommSq_of_mem_closure_range
    {Z S : Scheme.{u}} (j : Z ⟶ S) [QuasiCompact j] [IsImmersion j]
    {s : S} (hs : s ∈ closure (Set.range j)) :
    ∃ sq : ValuativeCommSq j, sq.i₂ (IsLocalRing.closedPoint sq.R) = s := by
  obtain ⟨z, hz⟩ := exists_specializes_of_mem_closure_range j hs
  let sq := ValuativeCommSqWithPt.ofSpecializes j hz
  exact ⟨sq.toValuativeCommSq, sq.closedPoint_eq⟩

end AlgebraicGeometry
