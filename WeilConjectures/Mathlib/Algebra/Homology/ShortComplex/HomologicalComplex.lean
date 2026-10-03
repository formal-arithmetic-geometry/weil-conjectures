/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exact functors preserve acyclicity

An exact functor between abelian categories preserves acyclicity of homological
complexes (`HomologicalComplex.Acyclic.map`).

If a homological complex `K` is exact at `j`, then `K.toCycles i j` is an epimorphism
(`HomologicalComplex.ExactAt.epi_toCycles`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- An exact functor preserves acyclicity of homological complexes. -/
lemma HomologicalComplex.Acyclic.map {ι : Type*} {c : ComplexShape ι}
    {M : HomologicalComplex C c} (hM : M.Acyclic) (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] :
    ((F.mapHomologicalComplex c).obj M).Acyclic :=
  fun i => ShortComplex.Exact.map (hM i) F

end CategoryTheory

namespace HomologicalComplex

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- If `K` is exact at `j`, then `K.toCycles i j : K.X i ⟶ K.cycles j` is an epimorphism. -/
lemma ExactAt.epi_toCycles {j : ι} (hj : K.ExactAt j) (i : ι) (hi : c.prev j = i) :
    Epi (K.toCycles i j) := by
  subst hi
  exact (K.sc j).exact_iff_epi_toCycles.1 hj

variable (K) in
/-- The short complex `K.cycles i ⟶ K.X i ⟶ K.cycles j`. -/
@[simps]
noncomputable def cyclesShortComplex (i j : ι) : ShortComplex C :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i j) (by
    rw [← cancel_mono (K.iCycles j), Category.assoc, toCycles_i, iCycles_d, zero_comp])

end HomologicalComplex
