/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Data.Countable.Defs
import Mathlib.Data.Set.Countable

/-!
# A countable DG subalgebra with unchanged cohomology

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
the construction of the countable DG subalgebra A-prime
(blueprint: lem-sfb-dg-countable-subalgebra).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace CategoryTheory.DgAlgebra

/-- An associative unital DG algebra with countable cohomology contains a countable
DG subalgebra inducing isomorphisms on cohomology. The subalgebra is represented
by a DG algebra and a degreewise injective DG algebra morphism into the ambient
algebra. Its degreewise images are additive subgroups containing the unit and
closed under multiplication and differential. Countability concerns the disjoint
union of the homogeneous pieces, retaining the degree of every element.

Source: Stacks Project, dga.tex, Tag 0CRM, lemma-countable, proof (2) to (1),
paragraph constructing A-prime (blueprint: lem-sfb-dg-countable-subalgebra).

Proof: First close a set of homogeneous elements under the unit, degree-tagged
zeros, negatives, same-degree sums, products and differential by iterating these
operations over the natural numbers. Maximum stages give closure under binary
operations; inclusion of generating sets gives inclusion of these closures.
If the generating set is countable, every stage and their union are countable
by `lem-trf-countable-unions`, using `def-sfb-countable-set` for countability.
Choose one cycle representing each cohomology class in every integer degree.
Their countable DG closure B_1 surjects onto all the cohomology of A.
Given B_n, choose an ambient primitive for each of its cycles that is a boundary
in A, and form the DG closure of B_n and these primitives. This is a countable
B_(n+1) containing B_n, and every such cycle becomes a boundary in B_(n+1).
The increasing union A_0 is a unital DG subalgebra and its degree-tagged set is
countable by `lem-trf-countable-unions`. The chosen cycles in B_1 prove
surjectivity on cohomology. A cycle in A_0 that becomes a boundary in A occurs
in some B_n and has its primitive in B_(n+1), proving injectivity. The actual
inclusion is a DG algebra morphism, so these are its induced cohomology maps.
-/
theorem exists_countable_quasiIso_subalgebra (A : Algebra.{u})
    (hcount : ∀ i : ℤ, Countable (A.X.homology i)) :
    ∃ (A₀ : Algebra.{u}) (ι : A₀ ⟶ A),
      (∀ i : ℤ, Function.Injective (ι.hom.f i)) ∧
      Countable (Σ i : ℤ, A₀.X.X i) ∧ QuasiIso ι.hom := by
  sorry

end CategoryTheory.DgAlgebra
