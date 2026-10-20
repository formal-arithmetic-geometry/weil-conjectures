## What changed

Completed the listed upstream-sync import repair and restored
Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare from its quarantine source.
Its complete theorem statement and docstring are preserved. The obsolete private
resolution import is replaced by the adopted resolution extension. ModuleCohomologyFMap
is a public import because the theorem statement uses its declaration.

The same obsolete private import is replaced in the two unclaimed support modules
CoherentEtaleComparisonMorphismExists and CoherentEtaleEffacingSequence. The current
CanonicalCoherentEtaleComparison source is preserved, with all its newly synchronized
public declarations; it compiled unchanged against the repaired supports. No source-tree
WeilConjectures file is changed. The existing naturality node is attached to the adopted
source incarnation of its unchanged theorem.

Validation: lcompile.py --all compiled both repaired supports, the unchanged current
canonical consumer, and the restored item (0.2, 0.2, 25.5 and 11.0 seconds respectively).
The repair changes imports only, so it neither alters normalization nor chooses any
new comparison data. No intermediate proof obligations are split off.

Change record: coord/changes/B3-qcoherent-normalized-pullback-resolution-imports.md.

## Proved and sorry left

Holes closed: 0. Holes added: 0. This is the dispatcher-marked repair assignment.
The restored item has its original one hole:
AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square
(node lem-weil-pbc-qcoherent-normalized-pullback-square).

The adapted support module retains its existing hole
AlgebraicGeometry.Scheme.Modules.CoherentEtale.exists_normalized_map
(node lem-pbc-coherent-etale-normalized-additive-map). It is neither added nor changed.
CoherentEtaleEffacingSequence has zero holes. The cohomological pullback theorem has
not been claimed proved: proving section-map naturality alone does not prove its
normalized cohomology square.

## No longer needed

The obsolete proof import
Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality is no longer needed by
these three modules; its adopted source replacement supplies the same interface.
No node or module is withdrawn. No mathematical proof dependency is pruned. The unit
route and all dependencies of the quarantined item remain intact. The obsolete module
itself is not deleted, nor is any adopted source declaration removed.

## Where the brief, the DAG or earlier work was wrong

The shared source changed during this session. A stale canonical-comparison copy
would have removed newly added public Ext-presentation declarations; that copy was
replaced with the exact current source and then omitted from this delivery because
it needed no edit. The rework failure was the duplicate imported declaration, not a
false statement in the restored theorem.

STATEMENT-DISPUTED: ringedSite_cech_refinement_square_rest lacks a hypothesis on
its arbitrary gamma (an issue found while investigating the proof plan). At degree zero on the one-object
site, take integer modules, h the identity, normalized edges identities and gamma zero:
the roof normalization forces hH to be the identity, while its edge square forces it
to be zero. The main refinement theorem prescribes gamma correctly, but this helper
needs that prescription as a hypothesis. This repair does not use the helper to prove
anything and makes no change to its independently assigned module.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
