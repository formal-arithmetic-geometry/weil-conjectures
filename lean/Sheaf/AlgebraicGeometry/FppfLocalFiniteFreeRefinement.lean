/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.Open
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Two-level finite locally free refinements of fppf coverings

Source: Stacks Project, More on Morphisms, Tag 05WN, lemma-dominate-fppf
(blueprint: lem-trf-fppf-local-finite-free-refinement).
-/

@[expose] public section

universe v u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An fppf covering admits two successive surjective finite locally free refinements,
with Zariski open coverings before and between them, whose composites factor through
members of the original family. Empty schemes and empty indexing families are allowed.

Source: Stacks Project, More on Morphisms, Tag 05WN, lemma-dominate-fppf
(blueprint: lem-trf-fppf-local-finite-free-refinement).

Proof:
1. For an empty base choose the empty first open cover; all remaining data are empty.
   An empty original family forces the base to be empty by joint surjectivity.
2. Apply lem-trf-fppf-etale-finite-free-refinement (Tag 0DET): obtain a jointly
   surjective etale family `E a → S`, surjective finite locally free maps `V a → E a`,
   and maps from `V a` into members of the original covering, commuting over `S`.
3. Apply lem-trf-etale-finite-free-open-refinement (Tag 02LI) to that etale family.
   It gives an open cover `U`, finite locally free surjections `q j : W j → U j`,
   and open covers `V j` of `W j` with maps to suitable `E a`, commuting over `S`.
4. For each pair `j, k`, pull back `V a → E a` along `V j k → E a`.
   Its projection `t j k` is finite locally free and surjective: finiteness, flatness,
   local finite presentation, and surjectivity are stable under base change, by
   lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-flat-morphism-base-change,
   clause (3) of lem-weil-pbc-qcqs-morphism-permanence, and
   lem-weil-pbc-surjective-base-change. This uses def-pc-fibre-product and
   def-pc-finite-locally-free, without any quasi-compactness or separatedness assumption.
5. Compose the other pullback projection with the map from `V a` to the chosen original
   member. The pullback relation and the equalities in steps 2 and 3 give the displayed
   equality of morphisms. Joint surjectivity follows successively from the two open
   covers and two surjections. The index sets and their dependent sums are small in
   the explicit universes, as in def-weil-size-convention. -/
theorem exists_finite_locally_free_fppf_refinement
    {S : Scheme.{u}} {I : Type v} (Si : I → Scheme.{u}) (f : ∀ i, Si i ⟶ S)
    (hf : Presieve.ofArrows Si f ∈ fppfPrecoverage S) :
    ∃ (U : OpenCover.{u} S) (W : U.I₀ → Scheme.{u}) (q : ∀ j, W j ⟶ U.X j)
      (V : ∀ j, OpenCover.{u} (W j)) (T : ∀ j, (V j).I₀ → Scheme.{u})
      (t : ∀ j k, T j k ⟶ (V j).X k),
      (∀ j, (q j).IsFiniteLocallyFree ∧ Surjective (q j)) ∧
      (∀ j k, (t j k).IsFiniteLocallyFree ∧ Surjective (t j k)) ∧
      ∀ j k, ∃ (i : I) (r : T j k ⟶ Si i),
        r ≫ f i = t j k ≫ (V j).f k ≫ q j ≫ U.f j := by
  sorry

end AlgebraicGeometry.Scheme
