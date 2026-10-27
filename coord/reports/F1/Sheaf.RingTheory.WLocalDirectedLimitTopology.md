## What changed

Proved `PrimeSpectrum.wLocal_directedLimit_topology` in
`Sheaf.RingTheory.WLocalDirectedLimitTopology`, preserving its statement and public imports.
The proof constructs compatible maximal specializations from stage w-locality, lifts them
through `AlgebraicGeometry.filteredSpectrumTopologicalLimit`, and detects prime inclusion
using specialization in the compatible-family subspace. It then proves the maximality
criterion, the closed-locus equality, and w-locality. Both canonical comparisons are
continuous bijections between compact and Hausdorff spaces. The component comparison uses
the existing proved `WLocalSpace.closedPointsHomeomorph` and
`WLocalSpace.closedPoints_eq_of_mk_eq` API. Updated the item's DAG proof accordingly.

Validation: the final module compiled through `lcompile.py` without warnings or errors
(3.3 seconds reported by the server).

All witnesses used in the proof are proof-local; no data definitions or arbitrary ring
constructions were introduced. The proof includes empty spectra and noninjective
transition maps: it never assumes a spectrum is nonempty, and obtains any point only
from a specified compatible family or a point already given.

## Proved and sorry left

Closed 1 of 1 original holes: `PrimeSpectrum.wLocal_directedLimit_topology`
(node `lem-sfb-wlocal-directed-limit-topology`). Added 0 holes; split off 0 theorems.
No `sorry` remains in the delivered module. The existing theorem
`AlgebraicGeometry.filteredSpectrumTopologicalLimit` remains an imported proof dependency;
its hole is unchanged and is not part of this delivery.

## No longer needed

Removed proof imports:
- `Sheaf.Topology.WLocalComponents`;
- `Mathlib.AlgebraicGeometry.AffineScheme`;
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`;
- `Mathlib.Topology.Spectral.Basic`;
- `Mathlib.RingTheory.Ideal.Maximal`.

The last two were redundant through retained imports. The source library already proves
the exact closed-point/component homeomorphism, so the larger bundle at
`det-pe-wlocal-components` / `Sheaf.Topology.WLocalComponents` is unnecessary for this
proof; the DAG now cites its existing source attachment
`lem-weil-pbc-w-local-closed-points-components-homeomorphism` instead.
`lem-weil-pbc-affine-scheme-qcqs` and `lem-weil-pbc-qcqs-scheme-spectral` are also
unnecessary here because spectrality is inferred directly for the prime spectrum.
No whole module is withdrawn, and no claim is made that other consumers no longer need
these declarations. The compatible-prime-family dependency remains necessary.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's product-subspace topology
calculation can be replaced by the compact-to-Hausdorff continuous-bijection theorem.
Its component bundle was stronger than needed: the source library already contains the
exact component homeomorphism. The unit's route is preserved; the unit record has no
realized statement or step attached to this auxiliary node.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
