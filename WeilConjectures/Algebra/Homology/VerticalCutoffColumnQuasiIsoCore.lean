/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictCases
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictPositive

/-!
# The strict endpoint case of the nested-cutoff comparison

The comparison from the cokernel of nested smart cutoffs to the window is a quasi-isomorphism
when the endpoints satisfy `a < b`.

## References

* Stacks Project, Homology, Section 12.15, Tag 0118 (canonical cochain truncations)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The strict endpoint case of the nested-cutoff comparison. -/
theorem verticalCutoff_column_quasiIso_strict
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a < b)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  by_cases ha : a ≤ 0
  · exact verticalCutoff_column_quasiIso_strict_nonpositive L a b hab ha g hg q hq
  · exact verticalCutoff_column_quasiIso_strict_positive L a b hab (lt_of_not_ge ha) g hg q hq

end HomologicalComplex₂
