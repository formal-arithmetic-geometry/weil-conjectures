module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.List

/-!
# Countable DG submodule representatives

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
the paragraph beginning “Assume A is countable”
(blueprint: lem-sfb-dg-countable-submodule-representative).

A DG submodule is expressed by a degreewise injective DG module map. Its image
in each degree is the corresponding actual subgroup of the ambient module.
The chain-map and module-map laws ensure stability under differential and action.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.DgAlgebra

/-- A DG module with countable cohomology over a countable DG algebra contains
 a countable DG submodule whose inclusion is a quasi-isomorphism.

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
the paragraph beginning “Assume A is countable”
(blueprint: lem-sfb-dg-countable-submodule-representative).

Proof plan:
1. Use injections into the natural numbers to show that subsets, images, products,
   and integer-indexed unions of countable sets are countable
   (def-sfb-countable-set and lem-trf-countable-unions).
2. For homogeneous T, generate G(T) by T and its differentials under finite sums
   and right multiplication. Include empty sums. The DG Leibniz identity shows
   that G(T) is stable under the differential.
3. If T is countable, finite lists of pairs of generators and homogeneous algebra
   elements encode every element of G(T). Thus its homogeneous set is countable
   (lem-sfb-countable-finite-lists and lem-trf-countable-unions).
4. Choose one cycle for each cohomology class in every degree. Generate a
   countable DG submodule M₀ from these; its cohomology maps are surjective.
5. From Mₙ, adjoin one ambient primitive for every homogeneous element of Mₙ
   which is a boundary in N, and generate Mₙ₊₁. Countability is preserved.
6. The increasing union M is a DG submodule and is countable by
   lem-trf-countable-unions. Closure follows by placing any finite list of
   elements in a common stage.
7. Surjectivity on cohomology follows from M₀. A cycle of M which bounds in N
   lies in some Mₙ, so its chosen primitive is in Mₙ₊₁. This gives injectivity
   on cohomology. The degreewise inclusions are injective DG module maps.
-/
theorem exists_countable_submodule_quasiIso (A : Algebra.{u})
    (hA : Countable (Σ i : ℤ, A.X.X i)) (N : RightModule A)
    (hN : ∀ i : ℤ, Countable (((underlying A).obj N).homology i)) :
    ∃ (M : RightModule A) (ι : M ⟶ N),
      (∀ i : ℤ, Function.Injective (((underlying A).map ι).f i)) ∧
      Countable (Σ i : ℤ, ((underlying A).obj M).X i) ∧
      QuasiIso ((underlying A).map ι) := by
  sorry

end CategoryTheory.DgAlgebra
