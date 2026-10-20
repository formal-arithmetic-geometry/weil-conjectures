## What changed

Retired Sheaf.RingTheory.ConormalExteriorModule in favor of the existing
WeilConjectures.RingTheory.ConormalExteriorModule, as requested by
coord/retire-items.tsv. The duplicate AlgebraicGeometry.conormalExteriorModule
is withdrawn through deleted.txt. The node new-r4-conormal-exterior-module now
records the upstream root-namespace conormalExteriorModule and the same concrete
construction. No source-library file is changed.

Checked consumers using tools/downstream.py and source searches: the current
tree has no importers of the retired module and no uses of its qualified
declaration outside its defining file. Existing unqualified uses in Sheaf's
affine wedge chart modules already import the upstream SelfTorAffineSection.
No consumer adaptations are needed.

The server compiled scratchpad/ConormalExteriorAudit.lean in 1.5 seconds. It
checks equality of the original bundled A-module and the upstream bundled
A-module by rfl for arbitrary A, I and n, including explicit degree-zero,
zero-ideal and unit-ideal cases. Both the upstream definition and the equality
have only propext, Classical.choice and Quot.sound as axioms. The scratch audit
is validation only and is not part of the delivery.

Change record: coord/changes/retire-conormal-exterior-module.md.

## Proved and sorry left

This is a zero-hole duplicate-definition retirement. Holes before: 0; holes
closed: 0; holes added: 0; holes remaining: 0. No theorem is split off. Neither
the withdrawn AlgebraicGeometry.conormalExteriorModule nor the retained upstream
conormalExteriorModule contains sorry.

## No longer needed

Sheaf.RingTheory.ConormalExteriorModule and its duplicate declaration
AlgebraicGeometry.conormalExteriorModule are no longer needed. Its three public
Mathlib imports disappear from the empty retired module; the unchanged upstream
module imports those same foundations for the retained construction. No consumer
import needs removal because all former consumers have already migrated.
The DAG node new-r4-conormal-exterior-module is retained and redirected to the
upstream declaration; no other node or module is pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe this zero-hole retirement item;
coord/retire-items.tsv supplies the concrete assignment. Its listed consumers
SelfTorAffineSection and SelfTorConormalComparisonPredicate have already been
retired from Sheaf in the current source tree. The node's old Lean attachment
still named the unused Sheaf declaration. The upstream declaration has the same
body but is in the root namespace, so the node's declaration name is updated
along with its module and file. No mathematical statement or unit route changes.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
