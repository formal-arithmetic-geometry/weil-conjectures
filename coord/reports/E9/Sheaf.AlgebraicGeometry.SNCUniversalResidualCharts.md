## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.nonempty_sncResidualAtlas` with a
point-indexed atlas assembly. The chosen point above each stratum point proves that the
residual chart projections form an etale covering. The canonical residual-map identity,
proved by cancelling the closed stratum immersion, identifies each lifted residual map
with its singleton pro-etale cover followed by the chart projection. Composition of
coverings and an explicit sigma-family reindexing prove the pro-etale covering assertion.
The finite common-refinement result supplies the atlas refinement field. The empty
stratum has the empty index type by construction.

Extracted the unchanged data block to `SNCResidualChartData` and re-exported it publicly
from the original module, avoiding circular imports by the two intermediate statements.
The extraction was checked byte-for-byte against the original declaration block.
No declaration in lean/WeilConjectures was changed. The already proved
`snc_strictLocal_roots_connected` and its domain-theorem proof are preserved.

Two separate mathematical results remain as named public statements: existence of one
chart above a prescribed stratum point, and existence of one common refinement of a
finite pointed family. Neither states an atlas or a covering-family assertion. The
pointwise result has no refinement assertion; the refinement result has no assertion
that the family covers the stratum. They are strictly separate parts of the original
argument. The proof combining them is written in Lean in the item module.
The final item compile passed with no diagnostics in 6.9 seconds; the data module
and both intermediate statement modules also compiled. Signatures and the original
strict-local proof were compared verbatim. Consumer compatibility is by the unchanged
public re-export, with every downstream consumer and its current holder in the change record.

## Proved and sorry left

Original item: one hole, `AlgebraicGeometry.ProEtale.nonempty_sncResidualAtlas`.
Closed that hole by decomposition into two separate results, not by a complete proof
of their underlying geometry. Preserved the previously proved
`AlgebraicGeometry.ProEtale.snc_strictLocal_roots_connected`.

Added two holes, each exactly `:= by sorry` in its own public theorem:

- `AlgebraicGeometry.ProEtale.exists_sncResidualChart_at`, node
  `lem-sfb-snc-pointwise-residual-chart`, module `SNCPointwiseResidualChart`.
- `AlgebraicGeometry.ProEtale.exists_sncResidualChart_common_refinement`, node
  `lem-sfb-snc-residual-chart-common-refinement`, module
  `SNCResidualChartCommonRefinement`.

Actual packet hole count: two, both listed above; zero in definitions, structures,
private declarations or the item module. Holes closed: one. Holes added: two.
This is a decomposition with net closure -1, not a net hole reduction.

## No longer needed

No mathematical dependency module is claimed pruned. The original direct public
imports now belong to the data module and remain publicly available through it.
The original proof import `Sheaf.RingTheory.HenselianParameterRootDomainTower` remains
needed by the strict-local companion.

The pointwise existence node owns the affine-stratum, henselian pointed-cover,
regular-stage ascent, compatible-unit-root, root-domain and punctured-cover-tower
dependencies. The finite refinement node owns the pointed affine common-refinement,
compatible-unit-root and unit-coordinate comparison dependencies. These nodes remain
needed, even though the atlas assembly imports only the two new statements.
No unit statement or realized step is bypassed; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The plan provides the geometric ingredients but does not
state the interfaces that assemble them into the full SNCResidualChart structure or
into SNCResidualRefinement. In the attempted direct construction, the remaining glue
includes transporting the affine residual pullback through the stratum open, aligning
the finite-stage coefficient algebra instances, identifying the two iterated quotient
ideals and canonical quotient maps, and changing the marked geometric points of the
input universal covers in a finite common refinement. These are substantive missing
interfaces; the two new nodes record their geometric conclusions with source proofs.
No compiler time limit is changed, and the data extraction is for acyclic imports.

## New nodes

`lem-sfb-snc-pointwise-residual-chart` isolates original steps 1–16 and 21 for one
stratum point, with the existing six declared geometric/root-theoretic ingredients.
It includes the empty-label and order-one cases. A point of an empty stratum cannot
be supplied, so the empty-stratum case is vacuous.

`lem-sfb-snc-residual-chart-common-refinement` isolates original steps 19–20, including
zero input charts and zero labels, and makes the canonical base and lifted-point
squares explicit. It uses the existing pointed affine common-refinement and unit-root
comparison interfaces.

Change record: `coord/changes/E9-snc-residual-data-relocation.md`. The existing data
node's Lean attachment is relocated; the item node's proof dependencies and proof
steps now follow the Lean atlas assembly.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
