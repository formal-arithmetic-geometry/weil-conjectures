## What changed

Restored lean/Sheaf/AlgebraicGeometry/PicardKunnethCechModels.lean from the precise
quarantine path in coord/rework.tsv. Replaced its withdrawn public Sheaf field-linear
operations import with the adopted WeilConjectures module containing the same
operations. The sole theorem, picard_kunneth_cech_models, and its complete proof are
otherwise verbatim. This fixes a reproduced compiler failure in the archived source;
it is a restoration repair, not a no-op or a rebase.

The three existing declared proof dependencies supply the actual scalar models,
the normalized cochain realization, and geometric invertibility. The original
assembly already is the short route from these declarations. Lean Finder returned
no scheme-specific substitute; Loogle confirmed the homology-map API. Source grep
found the already-adopted resolution/cochain constructions. No new mathematical
route is needed. Reviewed the node, its three dependency nodes and their signatures,
the cube unit record, and Stacks varieties-lemma-kunneth/equation-kunneth-on-cech.

The corrected item compiles cleanly in 3.8 s. A separate sandbox probe compiled the
entire archived PicardKunnethQcohIso consumer proof with its own obsolete public
field-linear import migrated in the probe only. It compiled in 4.6 s against the
restored item (5.4 s in that overlay). No consumer adaptation is delivered. Both
axiom prints show propext, Classical.choice, Quot.sound and inherited sorryAx.

Change record: coord/changes/R4-picard-kunneth-cech-models-restoration.md.

## Proved and sorry left

The quarantined starting module has zero sorry bodies; the restored module has zero.
Holes closed: 0. Holes added: 0. Split off: 0. No remaining sorry declaration in this
packet. The complete proof of AlgebraicGeometry.Scheme.Modules.picard_kunneth_cech_models
is preserved, with node lem-sc-picard-kunneth-cech-models. Existing dependencies still
account for sorryAx; this packet does not claim their proofs are finished.

## No longer needed

Removed direct import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations,
which is now a withdrawn empty module. Its replacement is the actual adopted source
module, WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations.
No mathematical node or module is pruned or withdrawn. All three proof dependencies
are retained: lem-sc-picard-kunneth-resolution-model,
lem-sc-picard-external-cup-cochain, lem-sc-picard-external-cup-quasi-iso. The existing
node attachment, proof, proof_deps and proof_origin remain accurate unchanged.

## Where the brief, the DAG or earlier work was wrong

This is an explicit quarantine rework assignment with zero local holes, rather than
an unfinished proof. The archived module's public import was stale after adoption
of the field-linear operations into WeilConjectures. The original compile reports
scalarCohomology and externalCup as privately imported and requests the new public
import. Restoring the archive unchanged would not repair the issue.

The archive and its Lean attachment are retained. The sole DAG parent and Lean
consumer is the quarantined PicardKunnethQcohIso, so zero live importers provides no
withdrawal justification. No statement, definition or unit route is changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
