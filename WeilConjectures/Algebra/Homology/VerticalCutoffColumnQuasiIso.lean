/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoCore
import WeilConjectures.Algebra.Homology.VerticalCutoffColumnQuasiIsoEqual

/-!
# Quasi-isomorphism of the cokernel of nested vertical cutoffs

The canonical projection on a single column induces a quasi-isomorphism from the cokernel of
nested smart cutoffs onto the corresponding window.

## References

* Stacks Project, Homology, Tag 0118 (canonical cochain truncations)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical projection on a single column induces a quasi-isomorphism on the
quotient of nested smart cutoffs. -/
theorem verticalCutoff_column_quasiIso
    (L : CochainComplex C ℕ) (a b : ℤ) (hab : a ≤ b)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  rcases hab.lt_or_eq with hablt | rfl
  · exact verticalCutoff_column_quasiIso_strict L a b hablt g hg q hq
  · exact verticalCutoff_column_quasiIso_equal L a g hg q hq

end HomologicalComplex₂
