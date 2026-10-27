## What changed

Decomposed the whole-Roos transport argument into canonical comparison construction,
strict restriction coordinates, and derived cancellation on strict representatives.
The original point_system_roos_transport theorem is assembled from those three
subclaims. Its complete Lean proof extends the representative transport equality to
all derived objects using Localization.natTrans_ext, proves transport_model by
naturality of thetaR and the descent factorization, and proves the transition and
diagonal clauses with roosU_natural and roosF_map_χ.

Moved the existing interface, including the previously proved exact_products theorem,
unchanged into Sheaf.Paper.PointSystemRoosTransportData. The original module publicly
re-exports it. The new subclaims publicly import only this shared interface; imports
of existing normalized-comparison and whole-square results are private. No existing
public declaration signature, definition body or target statement changes. No source
library module is edited. No forced adaptations are needed.

## Proved and sorry left

This is a decomposition, not a net proof: one original hole is closed and three are
added (net minus two holes). The original module has zero remaining sorry bodies.
The closed declaration is WeilConjectures.PointSystemRoos.point_system_roos_transport
(node lem-trf-point-system-roos-transport). Its combination proof is complete.

The three remaining holes are exactly:

- WeilConjectures.PointSystemRoos.point_system_roos_comparison_assembly,
  node lem-trf-point-system-roos-comparison-assembly: construct and normalize comparison
  data, without asserting transport.
- WeilConjectures.PointSystemRoos.point_system_roos_restriction_assembly,
  node lem-trf-point-system-roos-restriction-assembly: compare the strict restriction
  cone and its section projections, without proving a derived transport identity.
- WeilConjectures.PointSystemRoos.point_system_roos_transport_representative,
  node lem-trf-point-system-roos-transport-representative: cancel normalized comparison
  isomorphisms at a localized strict complex, assuming the strict restriction square.

Each has a new module, an exact named public `:= by sorry` body, source attribution,
and the complete argument in words. None restates the original existence theorem:
the latter constructs all comparison data and proves six transport clauses. No new
hole is inside a definition. The existing exact_products proof is unchanged and is
not counted as a newly closed hole.

## No longer needed

No mathematical dependency, node or module is pruned. The old item's seven direct
public imports move to the shared interface and remain transitively public. Its
private NormalizedComparisonData import is retained by that interface for the
existing exact_products proof. The old private PointRestrictionWholeRoosSquare
import is used by the two relevant new assembly modules. These are relocations,
not claims that the imported mathematics is unnecessary.

The original statement's DAG parents and the unit route are retained. No file is
withdrawn. Current absence of Lean importers was not used as a pruning argument.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The new subclaims were checked on the zero complex,
identity morphisms and the least allowed power r=1: they reduce to the same canonical
product and cone identities. No boundedness, cartesianness or faithful evaluation
hypothesis is used. Product and diagonal laws fix both cone coordinates, so the
restriction assertion does not permit an independent sign choice. The original DAG's final assembly step conceals three
separate compatibility arguments. Product projection equations must identify both
cone coordinates; equality of derived maps cannot be inferred merely from evaluation
at the coefficient levels. The representative lemma records the required conjugation
and cancellation before localization extends the equality to all derived objects.

The existing source path names the historical agent refinement; the newest blueprint
transport proof was also checked. This delivery keeps that refinement and the same
unit route. There is no permission request or unresolved tooling workaround.

## New nodes

- def-trf-point-system-roos-transport-data attaches the unchanged explicit interface
  to its new shared module. The prior exact-products proof and dependency are kept.
- lem-trf-point-system-roos-comparison-assembly isolates construction and normalization
  from NormalizedComparisonData and the strict restriction transformation.
- lem-trf-point-system-roos-restriction-assembly isolates projection extensionality and
  the actual restriction on strict cones, using PointRestrictionWholeRoosSquare.
- lem-trf-point-system-roos-transport-representative isolates derived cancellation on
  localized strict complexes, using the existing descent factorization.

Change record: coord/changes/Q2-point-system-roos-data-interface.md.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
