/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Cohomology in a weak Serre class

Source: Stacks Project, Tag 06UQ, label `lemma-cohomology-in-serre-subcategory`,
`derived.tex:5935-5960` (blueprint: lem-sbc-cohomology-in-weak-serre-subcategory).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory

/-- If `P` is a weak Serre class in an abelian category, the derived objects whose
cohomology lies in `P`, together with their bounded-below and bounded intersections,
form full triangulated subcategories. (blueprint: lem-sbc-cohomology-in-weak-serre-subcategory)

Source: Stacks Project, Tag 06UQ, `lemma-cohomology-in-serre-subcategory`, with the
weak Serre hypotheses expanded by Homology, Tag 0754.

Proof, following the seven steps of the node:
1. The subcategory is full by construction. Functoriality of each cohomology functor
   transports membership across isomorphisms, using strict fullness of `P`. The zero
   object has zero cohomology, hence belongs to the subcategory
   (`def-weil-abstract-derived-category`).
2. For all integers `k` and `q`, the cohomology-shift isomorphism identifies the
   degree `q` cohomology of `K[k]` with the degree `q + k` cohomology of `K`.
   Isomorphism closure gives stability under every shift, including negative shifts
   (`lem-sp-derived-cohomology-shift`).
3. For a distinguished triangle `X → Y → Z → X[1]` with `X` and `Z` in the
   subcategory, the long exact cohomology sequence gives the five-term exact row
   `H^(q-1)(Z) → H^q(X) → H^q(Y) → H^q(Z) → H^(q+1)(X)`.
   Its four outer terms satisfy `P` (`lem-sf-derived-homology-long-exact`).
4. Denote the four maps by `a`, `b`, `c`, `d`. Put `U = coker a` and `V = ker d`.
   Exactness identifies `U` with the coimage of `b`; the coimage-to-target map
   is mono (`lem-weil-pbc-coimage-mono`). Its image is `im b = ker c`.
   The factor of `c` through `V = im c` is epi and still has kernel `ker c`,
   since the inclusion of `V` is mono. Thus `0 → U → H^q(Y) → V → 0` is short
   exact, by the abelian kernel, image and cokernel identifications (`def-sp-abelian`).
5. Cokernel closure puts `U` in `P`, and kernel closure puts `V` in `P`.
   Extension closure applied to this short exact sequence puts `H^q(Y)` in `P`.
   This holds in every integer degree, so `Y` belongs to the subcategory.
6. Containment of zero, shift stability and this triangle closure give the inherited
   triangulated structure by `def-weil-triangulated-subcategory`, since the ambient
   derived category is triangulated. Strict fullness was established in step 1.
7. Each of the bounded-below and bounded properties contains zero and is stable
   under shifts and distinguished triangles (`def-weil-pbc-bounded-derived-subcategories`).
   Their intersections with the cohomology property therefore contain zero and are
   shift-stable; for a triangle with outer vertices in either intersection, its
   middle vertex belongs to both factors by steps 3--5 and bounded triangle closure.
   The same full-triangulated-subcategory criterion gives both inherited structures.
-/
lemma cohomology_in_weak_serre_subcategory
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions] :
    (DerivedCategory.homologyProperty P).IsTriangulated ∧
      ((DerivedCategory.homologyProperty P ⊓
        DerivedCategory.TStructure.t.plus).IsTriangulated) ∧
      ((DerivedCategory.homologyProperty P ⊓
        DerivedCategory.TStructure.t.bounded).IsTriangulated) := by
  sorry

end CategoryTheory
