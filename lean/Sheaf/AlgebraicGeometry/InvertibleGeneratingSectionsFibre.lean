/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Sheaf.AlgebraicGeometry.Ample

/-!
# The fibre criterion for generating an invertible module

Source: Stacks Project, Modules, Definition 01AM and Lemma 01CY; Sheaves, Lemma 0H7H(2)
(blueprint: lem-weil-pbc-invertible-generating-sections-fibre).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The sections `s 0, …, s n` generate an invertible module if and only if at every point
one has nonzero residue-field value, equivalently their nonvanishing loci cover the scheme.
The value is nonzero exactly when the germ lies outside the maximal ideal times the stalk,
which is the definition of `nonvanishingLocus`. Compatible sections in `L.sections` are
identified with global sections by evaluation at the terminal open `⊤`.

Source: Stacks Project, Modules, Definition 01AM and Lemma 01CY; Sheaves, Lemma 0H7H(2)
(blueprint: lem-weil-pbc-invertible-generating-sections-fibre).

Proof:
1. By def-weil-pbc-generating-sections and lem-weil-pbc-locally-surjective-iff-stalks,
the free-module map is an epimorphism exactly when it is surjective on every stalk.
2. Its stalk image is the span of the germs of the sections. Finite tuples of germs
have representatives on a common open neighbourhood, by finite intersection.
3. By def-sc-invertible-module, each stalk is free of rank one over the local ring.
Its quotient by the maximal ideal is one-dimensional over the residue field
(def-weil-residue-field), and is canonically the tensor product with that field.
4. By lem-weil-pbc-nakayama-local-generators, the germs span the stalk exactly when
their classes span this residue-field quotient.
5. In a one-dimensional vector space, these classes span exactly when one is nonzero,
i.e. the point belongs to one of the nonvanishing loci.
6. Combining these equivalences at every point gives both the fibre criterion and
the union criterion. -/
theorem invertible_generating_sections_fibre_criterion (Y : Scheme.{u}) (L : Y.Modules)
    [L.IsInvertible] (n : ℕ) (s : ULift.{u} (Fin (n + 1)) → L.sections) :
    (Epi (L.freeHomEquiv.symm s) ↔
      ∀ y : Y, ∃ i, y ∈ nonvanishingLocus L ((s i).val (Opposite.op ⊤))) ∧
    (Epi (L.freeHomEquiv.symm s) ↔
      (⋃ i, nonvanishingLocus L ((s i).val (Opposite.op ⊤))) = Set.univ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
