## What changed

Proved `AlgebraicGeometry.exists_open_finite_irreducibleComponents` in
`Sheaf.AlgebraicGeometry.LocallyNoetherianComponentsLocallyFinite`, preserving its statement,
visibility, documentation and imports. Choose an affine neighbourhood of the given point,
use local Noetherianity to make its section ring Noetherian, and obtain a Noetherian
underlying space. Restriction sends every ambient component meeting the neighbourhood to
an irreducible component of the neighbourhood. Recovering the ambient component as the
closure of its restricted image proves injectivity; `Set.Finite.of_injOn` gives finiteness.

The single-file compile through `lcompile.py` passed without warnings. The argument uses
only Mathlib, with no project theorem whose proof still contains `sorry`.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.exists_open_finite_irreducibleComponents`
(node `lem-sc-locnoeth-components-locally-finite`).
Added zero holes. No `sorry` remains in the delivered module. No split-offs.

## No longer needed

None. No imports were added or removed. All declared proof dependencies are used:
`pqf-def-locnoeth` through `IsLocallyNoetherian.component_noetherian`;
`lem-sc-affine-noetherian-underlying-space` through `noetherianSpace_of_isAffineOpen`;
`lem-sc-noetherian-finite-irreducible-components` through
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`; and
`lem-sc-components-open-injection` through `preimage_mem_irreducibleComponents` and
`closure_image_preimage_of_isPreirreducible`. These are all provided by the existing
Mathlib import. The DAG proof and its dependencies already describe the implemented route,
so no node update is needed. No modules or nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The stated plan is implemented directly. The source's Noetherian-space finite-component
result was checked in `literature/stacks-project/topology.tex`, `lemma-Noetherian`, clause 2.
The unit record has no realized statement or steps bypassed by this proof.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
