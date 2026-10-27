## What changed

Filled `AlgebraicGeometry.Scheme.quasiAffineChartLimitTopology` from the declared
filtered-spectrum topological-limit and open-affinization-square theorems.
Naturality builds the compatible coordinates; the homeomorphism supplies the
continuous map and its uniqueness. A single chart proves the embedding. Directed
common upper bounds identify the chart lifts in the ambient scheme and establish
the range formula. Point lifting in the cartesian affinization square proves the
image formula for every ambient open, without a compactness assumption on that open.

Validation: `lcompile.py` compiled the complete proof successfully (12.1 seconds).

The section-ring diagram, theorem signature, and public imports are unchanged.
The proof follows the existing six-step node route and adds no node or declaration.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.quasiAffineChartLimitTopology`
(node `lem-a1-quasi-affine-chart-limit-topology`).
No holes remain in the item; no holes were added or split off.

The proof uses the existing declarations
`AlgebraicGeometry.filteredSpectrumTopologicalLimit` and
`AlgebraicGeometry.Scheme.isPullback_toSpecΓ_of_isOpenImmersion`, whose proofs
remain outside this delivery. This is a proof from the stated dependencies.

## No longer needed

None. Both existing private Sheaf imports and all five declared proof dependencies
are used. No module or node is withdrawn or pruned. No additional theory is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The cartesian-square argument is applied
only between the quasi-affine charts; the arbitrary ambient open is handled by
point lifting, so its quasi-compactness is never assumed. The actual restriction
maps of the section-ring diagram match `Scheme.toSpecΓ_naturality`.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
