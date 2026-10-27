## What changed

Implemented AlgebraicGeometry.Etale.SfDiagonalKernel.triangles from two independent
intermediate statements, preserving its complete signature. The Lean proof factors the
specified unit into diagonal insertion and kernel comparison, applies the two coordinate
contractions, uses the insertion/projection equations, and cancels tensor with each normalized
integral. The category-theory cancellation helpers and the unit factorization are proved.

SfSupportedDiagonalData contains the original eight public definitions. Seven are moved
verbatim, including their docstrings and bodies. The unit uses the same canonical maps,
reassociated into insertion followed by comparisonIso; comparison is its component. This
avoids the expensive concrete-functor reduction of the earlier component factorization.
SfDiagonalKernelIntegrals publicly re-exports them
and retains both original public imports. Additional explicit maps name the outside-first
projection, direct-image coordinate interchange, kernel comparison, and diagonal insertion.
A pointwise insertion API names its target as the pushed-forward kernel.
The right unitor has an API over general coefficients with domain explicitly written
using derivedTensorUnit. The component formulas retain the literal pullback/tensor
composite: abbreviating its computed object caused expensive kernel conversion. These
APIs avoid that conversion without changing the maps.
The extraction lets the two bridge statements import common data independently without
an import cycle or duplicate constructions. The data file retains the original public
import environment, including the ordinary coordinate contractions.

SfSupportedTraceContractions states the compact-support form of the existing ordinary
coordinate contractions, before diagonal insertion. SfDiagonalInsertionProjection states
projection naturality for an arbitrary supported class, before any trace or normalization.
Both follow the original proof plan and source. The unclaimed direct importer
SfP1IntegralTransportData is split to keep compilation within the limit: supportedMap
moves with unchanged signature, attribute and body into SfP1SupportedExtMapData and is
publicly re-exported. Every other declaration of that importer remains verbatim.

The original node explicitly cites the extracted data node as a statement dependency.
Change records: coord/changes/A4-sf-diagonal-kernel-data.md and
coord/changes/A4-sf-p1-supported-ext-map-extraction.md.

Validation: lcompile.py --all accepted all 16 modules: the six delivery files and
ten unchanged consumer copies. This includes every direct importer of both changed
existing modules and the two additional unit/counit users. No consumer adaptation was
needed. The unchanged check copies and all diagnostic modules were removed afterward.

## Proved and sorry left

Closed one original hole: AlgebraicGeometry.Etale.SfDiagonalKernel.triangles
(lem-sf-diagonal-kernel-integral-triangles), by a complete Lean assembly from the bridge
statements. Its module has zero remaining holes. The data API lemmas unit_app_eq and
counit_app_eq are proved, as are the private normalized_insertion,
normalized_pushed_insertion and their two wrappers retaining identity-functor objects. The component API confines its local
instance and reducibility settings to local sections in the data and triangle modules.

Added two holes, each the whole proof of one public theorem in its own module:

- AlgebraicGeometry.Etale.SupportedTrace.contractions
  (lem-sf-supported-trace-contractions; SfSupportedTraceContractions).
- AlgebraicGeometry.Etale.SupportedTrace.insertion_projection
  (lem-sf-diagonal-insertion-projection; SfDiagonalInsertionProjection).

This is a decomposition, not a completed proof without new holes: one hole closed,
two added, net closed-minus-added -1. SfSupportedDiagonalData,
SfP1SupportedExtMapData and SfP1IntegralTransportData contain no sorry.

## No longer needed

None. No module, declaration, or mathematical dependency is pruned. The six original
proof dependencies are retained in the two bridge nodes' proof plans. They are no longer
needed directly by the assembly proof, which uses the two strictly partial statements.
Both original public imports are retained to preserve the existing interface.

## Where the brief, the DAG or earlier work was wrong

The stated coordinate contraction theorem uses ordinary direct image, while this item
uses compact support and its specified composition maps. Its application requires the
proper comparison transport, not just matching the endpoints of an isomorphism. The
abstract ringed projection-section theorem likewise needs a concrete specialization to
these diagonal insertion maps. The two new statements expose these separate steps rather
than claiming they are solved by definitional reduction.

The contractions have no integral-normalization hypothesis, and no diagonal-class map
occurs in their formulas (only the trace field of the supplied datum). The insertion
statement has no trace or lisse/even-shift hypothesis, and concerns arbitrary delta.
Neither new statement is the original triangle assertion with renamed hypotheses.

Edge-case checks: for delta=0 the insertion formulas are equalities of zero maps, not
identity claims; for f=id they reduce to tensor naturality and unitor cancellation. The
zero coefficient ring and empty schemes introduce no extra assumption. The even-shift
condition is retained only where the ordinary contraction theorem needs self-symmetry.
The original unit's source composition comparisons and both original integral hypotheses
are retained explicitly throughout the assembly.

## New nodes

- def-sf-supported-diagonal-calculus: the common canonical data, including the verbatim
  extracted definitions, in SfSupportedDiagonalData. No existence witness or proof hole
  is used to choose data.
- lem-sf-supported-trace-contractions: proper forget-supports transport and factor-order
  transport of CoordinateTrace.contractions, before any diagonal insertion.
- lem-sf-diagonal-insertion-projection: projection naturality and the section identities
  for Delta and each coordinate, before tensoring with a trace or using integral one.
- def-sf-p1-supported-ext-map-data: the existing canonical supportedMap, extracted
  verbatim to keep its independent kernel checks separate from the other transport data.

The unit route is unchanged. The generic ringed tensor/projection tools were already in
the original proof plan; their use is recorded in the new nodes' split_report.tool_uses.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
