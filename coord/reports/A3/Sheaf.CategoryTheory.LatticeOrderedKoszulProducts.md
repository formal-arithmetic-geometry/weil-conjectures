## What changed

Replaced the hole in
`Profinite.DiscreteLattice.OrderedKoszul.lattice_ordered_koszul_products`
with an assembly from three strictly smaller statements, each in its own new module:
`KoszulSingleTensorNormalization`, `KoszulTrivialSubsetDecomposition`, and
`KoszulSubsetShuffleBinary`. Their docstrings and nodes give the source, full
natural-language proof, and edge cases. No existing signature or definition changed.

The item itself proves zero differentials from the Koszul matrix formula; extracts
K-flatness directly from the given cup comparison; proves the increasing-list
identity by induction, disjointness, and vanishing of the inversion filter; and
proves both derived identities using tensorator naturality and additivity. In fact,
its private localization lemma works for every list, without monotonicity.
The induction and localization arguments are complete Lean proofs, not new holes.
All the existing normalization, empty-unit, and rank-zero fields are retained.

The new modules state existence only of coordinate-normalized maps and isomorphisms.
No definition selects an arbitrary witness from an unproved existence statement.
The item destructs these theorems within its proof of a proposition.

Validation: all four modules compiled through `lcompile.py` without warnings.
The item took 27.0 seconds; the three new modules took 11.9, 12.7, and 13.2
seconds. Existing signatures and non-theorem bodies were compared with the shared
source and are unchanged. Node Lean signatures and proof-dependency unions agree.

## Proved and sorry left

Original holes: 1. The item's declaration
`Profinite.DiscreteLattice.OrderedKoszul.lattice_ordered_koszul_products`
has a complete proof from the three intermediate statements below. The item now
contains zero `sorry`. This is a decomposition, not a net reduction in holes:
one upper hole closed, three lower holes added (net minus two).

Every remaining hole added by this delivery:

- `Profinite.DiscreteLattice.OrderedKoszul.single_tensor_normalization`, node
  `lem-sfb-koszul-single-tensor-normalization`, module
  `Sheaf.CategoryTheory.KoszulSingleTensorNormalization`: only shift/tensor
  normalization and the K-flat localization comparison for single regular complexes.
- `Profinite.DiscreteLattice.OrderedKoszul.trivial_subset_decomposition`, node
  `lem-sfb-koszul-trivial-subset-decomposition`, module
  `Sheaf.CategoryTheory.KoszulTrivialSubsetDecomposition`: only the subset
  decomposition, empty unit, and rank-zero inverse, assuming vanishing differentials.
- `Profinite.DiscreteLattice.OrderedKoszul.subset_shuffle_binary`, node
  `lem-sfb-koszul-subset-shuffle-binary`, module
  `Sheaf.CategoryTheory.KoszulSubsetShuffleBinary`: only the binary shuffle
  calculation, for any maps satisfying the prescribed inclusion and tensor coordinates.

These three statements have distinct inputs and conclusions. None asserts Products,
ordered iteration, or its derived identities. Empty subsets, rank zero, the zero
ring, and characteristic two were checked against their componentwise arguments.

## No longer needed

Removed the item's direct proof imports
`Sheaf.CategoryTheory.RelativeTensorFiniteFreeCoordinates` and
`Mathlib.Algebra.Homology.BifunctorShift`. Their roles are now confined to the binary
coordinate and single-term normalization subproblems, respectively; their mathematics
has not been declared unnecessary throughout the DAG.

The former step of specializing the existential flat-algebra cup theorem, and
proving flatness of the regular module for that application, is unnecessary here:
the item already receives the exact cup comparison, including its K-flatness field.
No existing module is withdrawn. No global module pruning is claimed. The unit
route is unchanged; only this lower-level argument is decomposed.

## Where the brief, the DAG or earlier work was wrong

The original plan's step 2 overlooks that the Lean theorem takes the required cup
comparison as an input, so its K-flatness need not be reconstructed from the
existential cup-comparison theorem. The later coordinate calculation still needs
the cup's actual matrix normalization, which remains an explicit input.

No false statement or target-signature defect was found. Searches found useful
single-complex and graded tensor constructors, but no theorem assembling the
normalized internal-module statements. The exact internal-module reference remains
the existing node's explicitly agent-formulated proof; it is not attributed as a
new theorem asserted by blueprint paragraph (3). Stacks Tag 0FNH supplies the shift
convention. The latest blueprint's paragraph (3) and the unit record were read.
Blueprint searches for single tensor and subset shuffle found no matching node;
the ancestor tool reports no imported blueprint ancestor for this existing item.

## New nodes

`lem-sfb-koszul-single-tensor-normalization` isolates the source argument's step 3
and the single-complex K-flat assertion from step 6. It has no lattice-rank input.

`lem-sfb-koszul-trivial-subset-decomposition` isolates step 1 and the empty-unit
normalization. It assumes the differential vanishes and asserts no multiplication
formula or localization identity.

`lem-sfb-koszul-subset-shuffle-binary` isolates step 4. It assumes the two
coordinate normalizations and asserts the binary formula only; the item's
increasing-list induction and localization are separate, fully proved arguments.

The existing node's proof, proof dependencies, and proof origin now follow this
Lean reduction. There are no changes to another existing module or node and no
shared-interface change record is required.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
