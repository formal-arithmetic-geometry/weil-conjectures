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
