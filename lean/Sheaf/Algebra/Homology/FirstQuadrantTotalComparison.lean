/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Columnwise comparison of first-quadrant total complexes

Source: Stacks Project, Homology, Tag 0133, finite diagonal argument.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace HomologicalComplex₂

/-- A columnwise quasi-isomorphism of first-quadrant bicomplexes induces a
quasi-isomorphism on their total complexes.
Source: Stacks Project, Tag 0133, Lemma 12.25.4 and its second-variable variant.
(blueprint: lem-sc-first-quadrant-total-column-comparison).

Proof: extend the bicomplexes by zero to integer indices and form the columnwise
mapping cone of the morphism. Each column cone is acyclic by the hypothesis.
The cone bicomplex is bounded below in both directions (its resolution degrees
start at -1). Its total complex identifies with the cone of the total map:
in each degree both have the same finite summands, and the cone differential
and total differential agree after the standard sign change on the shifted
source summands. Filter this total by the second degree. The graded pieces
are shifts of the acyclic column cones. Translate the lower bounds to zero
and apply the first-quadrant spectral sequence: its first page vanishes,
so all its stable terms vanish. In degree n the filtration is finite; starting
with its zero last step, induction through its zero graded pieces gives zero
homology of the total cone. The cone criterion gives the asserted quasi-isomorphism.
No choice of an unproved existence witness enters any definition. -/
theorem quasiIso_totalMap_of_columns {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L)
    (hf : ∀ n : ℕ, QuasiIso
      (((flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f n)) :
    QuasiIso (total.map f (ComplexShape.up ℕ)) := by
  sorry

end HomologicalComplex₂
