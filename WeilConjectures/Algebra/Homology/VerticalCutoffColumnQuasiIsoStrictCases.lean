/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalTowerMaps

/-!
# The nonpositive endpoint case of the strict cutoff comparison

Reduction of the strict nested-cutoff comparison to the case where the lower endpoint is
nonpositive.

## References

* Stacks Project, Homology, Section 12.15, Tag 0118 (canonical cochain truncations)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The nonpositive endpoint reduction for the strict cutoff comparison. -/
theorem verticalCutoff_column_quasiIso_strict_nonpositive
    (L : CochainComplex C ℕ) (a b : ℤ) (_hab : a < b) (ha : a ≤ 0)
    (g : (verticalCutoff a).obj L ⟶ (verticalCutoff b).obj L)
    (_hg : g ≫ (verticalCutoffι b).app L = (verticalCutoffι a).app L)
    (q : cokernel g ⟶ (verticalWindow a b).obj L)
    (hq : cokernel.π g ≫ q = HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) : QuasiIso q := by
  have hzero : IsZero ((verticalCutoff a).obj L) := by
    rw [IsZero.iff_id_eq_zero]
    ext n
    change 𝟙 _ = 0
    apply IsZero.eq_of_src
    change IsZero ((CochainComplex.truncLE (L.extend ComplexShape.embeddingUpNat) (a - 1)).X
      (ComplexShape.embeddingUpNat.f n))
    exact CochainComplex.isZero_of_isStrictlyLE _ (a - 1) _ (by
      change a - 1 < (n : ℤ)
      omega)
  have hgzero : g = 0 := hzero.eq_of_src _ _
  have : IsIso (cokernel.π g) := by
    rw [hgzero]
    infer_instance
  have : CochainComplex.IsStrictlyGE (L.extend ComplexShape.embeddingUpNat) a :=
    CochainComplex.isStrictlyGE_of_ge _ a 0 ha
  have hmap : IsIso (HomologicalComplex.restrictionMap
      (CochainComplex.truncLEMap
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a) (b - 1))
      ComplexShape.embeddingUpNat) := by
    change IsIso ((ComplexShape.embeddingUpNat.restrictionFunctor C).map
      (((ComplexShape.embeddingUpIntLE (b - 1)).truncLEFunctor C).map
        (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) a)))
    infer_instance
  have : IsIso (cokernel.π g ≫ q) := by rw [hq]; exact hmap
  have : IsIso q := IsIso.of_isIso_comp_left (cokernel.π g) q
  infer_instance

end HomologicalComplex₂
