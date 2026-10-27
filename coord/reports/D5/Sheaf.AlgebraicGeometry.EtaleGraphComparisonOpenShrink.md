## What changed

Repaired the return of commit 0d6fba0bd4f (reviewer C-0d6fb). Removed the item’s
import and DAG dependency on EtaleGraphShrinkSidePasting. The current SidePasting
proof uses OpenShrink, so the earlier delivery was circular.

Proved the side equation directly in the assigned module. The fully proved private
side_square_pasting handles two Cartesian proper/open squares and proper graph lifts.
It extracts Cartesian normalization and the horizontal and vertical laws from
etaleProperOpenExchangeCube. The smaller side square is D_v followed horizontally
by D_H; the presentation triangle is E above D_v. Vertical pasting, followed by
naturality of the proper compositor, removes extension by the identity. Inverting
that equation gives the graph-triangle relation. Horizontal pasting and naturality
of the open compositor and of D_H reduce both side paths to the same D_v word.
Specialize to graphNeighborhoodShrink using its Cartesian and projection equations,
then whisker by the common outer proper image and use its compositor’s naturality.
Combine this side equation with the existing etaleGraphShrinkMiddlePasting using
the fully proved private shrink_cancel. The assigned theorem’s signature is
byte-identical to current main. No new module or public declaration is added.

Rechecked the earlier supporting edits. The InterchangeData public import swap
remains necessary even without SidePasting: MiddlePasting reaches InterchangeData,
whose BaseChange import otherwise reaches OpenShrink through pairwise normalization.
Keep the replacement by EtaleGraphPresentation and its dependency-only node repair;
all definitions and signatures stay verbatim. SfGraphCompactSupportCompositionBaseChange needs the direct BaseChange proof
import. Its original source with that import compiled once in 44.2 seconds, but
then failed the complete batch check at 96 seconds. Profiling with the direct
identity-law optimization took 59.8 seconds and showed roughly nine seconds in the
two normalized proper-pasting rewrites. Retain that private identity cancellation
and use rw instead of erw for those two equations to avoid unrelated unfolding.
Drop the DiagramPullback relocation and the graph_chosenExact_comp proof and option
changes. All definitions and signatures, and the public theorem’s proof, remain
verbatim. No profiling option or new transparency override is delivered.

Change record: coord/changes/etale-graph-interchange-definition-import.md.
The assigned node now records the direct cube calculation, neighborhood geometry,
MiddlePasting and cancellation, with no edge to SidePasting.

Validation: OpenShrink compiles with the normal transparency setting (10.7 seconds
alone, 36.4 seconds in the complete batch). The batch also passed InterchangeData
(25.9 seconds) and all three unchanged direct consumers: ComparisonInterchange
(29.1), NeighborhoodGeometry (37.0), ProductGeometry (41.2). The final consumer
compiles in 53.3 seconds with profiling removed and no warnings. The sandbox-overlaid Lean
import closure has no cycle. No DAG cycle contains either modified node; the returned
two-node cycle is removed. Identity and empty opens require no additional hypothesis:
the proof uses only the supplied Cartesian squares, isomorphisms and naturality.
The original unit route is preserved; sk-prop-sf-cbc has no individually realized steps.

## Proved and sorry left

Closed the one hole in current main:

- AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_openShrink
  (lem-pur-etale-graph-comparison-open-shrink).

The returned sandbox had zero literal sorries but an invalid circular proof. It now
has a complete noncircular proof. Added zero holes and split off zero statements.
All three delivered Lean files contain zero sorries. Both private helpers are proved.
The existing middle theorem uses etaleGraphShrinkFirstLeg and etaleGraphShrinkSecondLeg,
whose existing sorries remain in their own modules; this delivery does not move or
add those obligations.

## No longer needed

Removed Sheaf.AlgebraicGeometry.EtaleGraphShrinkSidePasting as an import and
lem-pur-etale-graph-shrink-side-pasting as a proof dependency of this item.
That theorem remains in the library for its other consumers; no module is withdrawn.

Removed the public BaseChange import and its theorem-node dependency from
InterchangeData, replacing them with the existing presentation interface. The actual
BaseChange theorem stays in the library, imported directly by its consumers.
Dropped the prior DiagramPullback relocation and graph_chosenExact_comp proof
and option changes. Retain only the private identity cancellation and two focused
proper-pasting rw changes after the original consumer exceeded the time limit.

The original def-pc-fibre-product and lem-weil-pbc-open-immersion-base-change
remain needed through the neighborhood geometry. The proper/open compositor and
exchange-cube dependencies remain needed in the direct side calculation. There is
no separate invocation of lem-weil-pbc-proper-base-change or
lem-weil-pbc-proper-to-separated: the graph words already prove graphS₂_proper,
and the proper projection instances are supplied by Mathlib. The separate
lem-amb-natural-transformation-whisker-exchange dependency is unnecessary: the proof
uses ordinary Mathlib naturality fields directly. The locally closed graph model
and the existing middle-pasting theorem remain needed. No unit or mathematical module
is pruned globally.

## Where the brief, the DAG or earlier work was wrong

The previous delivery treated SidePasting as an independent lower result. Current
main’s SidePasting derives its equation from OpenShrink and MiddlePasting, so that
route formed both an import cycle and a two-node DAG cycle. This repair implements
the original plan’s side-square step directly instead. The still-cyclic BaseChange
import in InterchangeData is independently unnecessary for its definitions and must
still be narrowed. The consumer initially passed with only its import change, but
failed the complete batch timing check, requiring a focused performance repair.
No mathematical statement, target signature or adopted source-library file changes.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
