## What changed

Proved `Topology.spectralSpace_directedLimit` in
`lean/Sheaf/Topology/SpectralDirectedLimit.lean`, preserving its entire signature and
all imports. Namespace openings are local to the proof. Compactness of cylinder opens and the limit uses the existing
`Topology.isCompact_limit_constructibleClosed` declaration. The rest is proved
using Mathlib: an intersection-stable cylinder basis, prespectrality and
quasi-separatedness from that basis, compatible generic points, and T0 separation
from the injective tuple map. Updated the node proof and theorem docstring to match.

Validation: the launcher single-file compile passed (2.7 seconds). The interface
comparison reports no changes to what importing modules see.

## Proved and sorry left

Closed 1 hole: `Topology.spectralSpace_directedLimit`
(node `lem-weil-pbc-spectral-directed-limit-spectral`). Added 0 holes and split off
0 statements. The delivered module has 0 `sorry`s. The existing dependency
`Topology.isCompact_limit_constructibleClosed` remains unproved in its own module;
this delivery uses its declared conclusion as intended by stage 3.

## No longer needed

No imports or declared dependency nodes were removed; all existing dependencies
remain needed. The old explicit single-stage descent argument for arbitrary compact
opens (old proof Step 3, Stacks 0A2Y) is unnecessary: Mathlib's
`QuasiSeparatedSpace.of_isTopologicalBasis` handles the finite-cover argument
internally. No additional import of `Sheaf.Topology.SpectralLimitDescendOpens` is
needed. No modules are pruned by this delivery. The unit's realized statements and
steps are unchanged; this node is below that level.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The planned proof was valid, but its separate
descent step and explicit generic-point uniqueness argument can be replaced by
existing Mathlib basis and T0 APIs. Edge cases are covered without extra
hypotheses: the empty compact open uses the same compactness argument; an empty
limit is allowed; nonemptiness is required only of the index, to put the whole
space in the cylinder basis; no surjectivity of transition maps is used.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
