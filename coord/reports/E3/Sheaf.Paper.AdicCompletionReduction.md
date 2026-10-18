## What changed

The interface change is recorded in `coord/changes/E3-adic-completion-reduction-interfaces.md`.

Added three named lower interface theorems to the item module. The derived scalar Hom
bijection is proved from the supplied Hom equivalence, and the completion reduction
isomorphism is proved from its restricted isomorphism and derived conservativity.
The existing concrete declarations and imports remain unchanged.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.Scheme.adicReductionAdjunction_bijective`.
- `AlgebraicGeometry.Scheme.adicCompletionReduction_isIso`.

Sorry left as explicit lower interfaces:

- `AlgebraicGeometry.Scheme.adicReductionAdjunction_homEquiv_exists`, node
  `lem-weil-pbc-adic-reduction-adjunction-hom-equiv`.
- `AlgebraicGeometry.Scheme.adicCompletionReduction_restricted_isIso`, node
  `lem-weil-pbc-adic-completion-reduction-restricted`.
- `AlgebraicGeometry.Scheme.adicDerivedRestrict_reflectsIsomorphisms`, node
  `lem-weil-pbc-adic-derived-restrict-conservative`.

## No longer needed

None. No imports or existing proof dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan leaves the derived adjunction, the restricted Koszul tower
calculation, and conservativity as separate mathematical interfaces. They were not
represented as Lean declarations, so this delivery records them as three strictly
lower nodes and proves the two original declarations from them.

## New nodes

`lem-weil-pbc-adic-reduction-adjunction-hom-equiv` records the canonical derived scalar
Hom equivalence and its unit formula.

`lem-weil-pbc-adic-completion-reduction-restricted` records the Koszul product-cone
calculation after restriction of scalars.

`lem-weil-pbc-adic-derived-restrict-conservative` records the exact conservative
restriction step on derived categories.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
