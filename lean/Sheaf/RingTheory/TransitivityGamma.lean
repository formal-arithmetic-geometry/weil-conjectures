/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.RingTheory.JacobiZariskiHomologySequence

/-!
# Left exactness of the Jacobi–Zariski sequence for fields

Source: Stacks Project, More on Algebra, Tag 07E2, `lemma-transitivity-gamma`
(blueprint: lem-weil-pbc-transitivity-gamma).
-/

@[expose] public section

universe u v w

namespace Algebra

/-- Source: Stacks Project, More on Algebra, Tag 07E2, `lemma-transitivity-gamma`
(blueprint: lem-weil-pbc-transitivity-gamma).

For a tower of fields, the entire Jacobi–Zariski sequence is exact, including its left
endpoint. Tensor factors are written with `M` first, as in
`Algebra.jacobiZariski_homology_sequence`; the symmetry sends `h ⊗ c` to `c ⊗ h`.
The left map sends `c ⊗ h` to `c • H1Cotangent.map K K L M h`, the map induced by
`K[L] → K[M]` on canonical presentations.

Proof, following the five steps of the DAG node:
1. Apply `lem-weil-pbc-jacobi-zariski-homology-sequence` to `K → L → M`. This gives
   exactness from the third term onward, with the canonical maps displayed below.
2. Over `L`, every vector space is free (`lem-weil-pbc-vector-space-free`), so its
   positive Tor groups vanish (`def-weil-pbc-tor-modules`). The Tor clause of the
   Jacobi–Zariski node identifies tensoring H1 with H1 of the tensored complex.
3. By `lem-weil-pbc-nl-presentation-h1-functoriality`, the first map is the composite
   of this identification with the map `u` of that sequence: both send a polynomial
   relation class tensored with `c` to `c` times its image under the variable inclusion.
   Thus its image equals the kernel of the next map.
4. For each complete-intersection `L`-subalgebra of `M`, apply
   `lem-weil-pbc-jacobi-zariski-regular-sequence-left-injective` to its regular-sequence
   presentation. The same identification gives injectivity at this finite stage.
5. For an element in the kernel at `M`, express it as a finite sum of pure tensors.
   Its vanishing is a finite sum of products of polynomial relations. All coefficients
   of the tensor expression and variables in those relations lie in some
   complete-intersection subalgebra by
   `lem-weil-pbc-field-extension-complete-intersection-subalgebras`. Canonical
   polynomial presentations (`def-weil-pbc-mv-polynomial-ring`,
   `def-weil-pbc-smooth-ring-map`) identify its relation ideal with the intersection
   of the relation ideal at `M` and its polynomial ring. The kernel element therefore
   vanishes already at that stage by step 4, and hence at `M`. -/
theorem transitivityGamma
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    Function.Injective ((H1Cotangent.map K K L M).liftBaseChange M) ∧
      Function.Exact ((H1Cotangent.map K K L M).liftBaseChange M)
        (H1Cotangent.map K L M M) ∧
      Function.Exact (H1Cotangent.map K L M M) (H1Cotangent.δ K L M) ∧
      Function.Exact (H1Cotangent.δ K L M) (KaehlerDifferential.mapBaseChange K L M) ∧
      Function.Exact (KaehlerDifferential.mapBaseChange K L M)
        (KaehlerDifferential.map K L M M) ∧
      Function.Surjective (KaehlerDifferential.map K L M M) := by
  sorry

end Algebra
