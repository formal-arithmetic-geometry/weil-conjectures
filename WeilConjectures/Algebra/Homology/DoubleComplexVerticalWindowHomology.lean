/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.Algebra.Homology.VerticalWindowSingleIso
import WeilConjectures.Algebra.Homology.DoubleComplexSingleRowTotalIso

/-!
# Total cohomology of a single smart vertical layer

The identification of the total cohomology of a vertical layer with the horizontal cohomology
of the vertical cohomology.

## References

* Stacks Project, Homology, Lemma "ss-double-complex", item (5)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Total cohomology of the vertical smart layer `[q,q+1)` is iterated cohomology. -/
theorem verticalWindow_total_homology_iso
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (p q : ℕ) :
    Nonempty ((HomologicalComplex₂.total
      (((verticalWindow (q : ℤ) (q + 1)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K) (ComplexShape.up ℕ)).homology (p + q) ≅
      (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).homology p) := by
  obtain ⟨e⟩ := verticalWindow_single_iso (C := C) q
  let L := ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K
  have eK := (NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app K
  obtain ⟨eT⟩ := singleRow_total_iso L q
  exact ⟨HomologicalComplex.homologyMapIso
    (HomologicalComplex₂.total.mapIso eK (ComplexShape.up ℕ)) (p + q) ≪≫
      HomologicalComplex.homologyMapIso eT (p + q) ≪≫
      L.extendHomologyIso (ComplexShape.embeddingUp'Add (1 : ℕ) q) rfl⟩

end HomologicalComplex₂
