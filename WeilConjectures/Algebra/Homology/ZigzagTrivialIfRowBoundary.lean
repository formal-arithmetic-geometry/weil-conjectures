/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Algebra.Homology.ZigzagZeroComponentBoundary
import WeilConjectures.Algebra.Homology.ZigzagBoundaryReduction

/-! # Exact-row zig-zags are trivial

## References

* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1), injectivity argument
-/

@[expose] public section

open CategoryTheory

namespace HomologicalComplex₂

universe u v

variable {R : Type u} [CommRing R]

/-- A zig-zag whose row-cokernel component is a vertical boundary is trivial when
all rows are exact in positive degrees. Here the row-cokernel complex is
`A.opcycles 0`, with projection `π = A.pOpcycles 0`, and `hboundary` says that `πₙ(a₀,ₙ)`
lies in the image of its differential. -/
theorem zigzag_trivial_if_row_boundary
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ) (a : zigzagTotal A n)
    (ha : a ∈ zigzagCycles A n)
    (hboundary : ∃ y : (A.opcycles 0).X (n + 1),
      (A.opcycles 0).d (n + 1) n y = (A.pOpcycles 0).f n
        (DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2) ⟨(0, n), by simp⟩ a)) :
    a ∈ zigzagBoundaries A n := by
  obtain ⟨b, hbz, hb0⟩ := zigzagBoundary_reduction A hrow n a ha hboundary
  have hbb := zigzag_zero_component_boundary A hrow n (a - zigzagBoundary A n b) hbz hb0
  obtain ⟨c, hc⟩ := hbb
  refine ⟨b + c, ?_⟩
  simp only [map_add]
  rw [hc]
  abel

end HomologicalComplex₂
