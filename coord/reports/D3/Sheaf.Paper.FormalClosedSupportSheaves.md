## What changed

Restored lean/Sheaf/Paper/FormalClosedSupportSheaves.lean from the quarantine path
recorded in coord/rework.tsv. Preserved its two real kernel-based definitions,
formal_closed_support_sheaves signature, all public imports, and Lean attachment.
The archived proof already had zero holes. Replaced its module extension-by-zero
open-unit argument with direct lifting of the abelian open counit through the
existing moduleCounitOfAbelian helper. Removed private helper openUnitIsIso and
replaced the private ModuleObject.LowerShriek.Defs import with
FiniteCoefficient.LowerShriek.Open.Defs. Updated the node's third proof step,
proof_deps, and proof_origin accordingly. The unit's sheaf-level support route is
preserved, including the canonical kernel, its natural closed unit, the actual
right adjunction, exact closed direct image, and unbounded K-injective preservation.

Validation: the archived proof compiled before the simplification; the shortened
proof compiled without warnings or errors in 9.5 seconds using lcompile.py.
Compared all three public signatures, both public definition bodies, and the
public-import list byte for byte with the quarantine source: all identical.
The replacement proof import passes import_direction.py. Searched LeanFinder,
Loogle, the Mathlib grep service, and local sources; the existing generic counit
and full-faithfulness API gives the shorter proof.

Change record: coord/changes/D3-formal-closed-support-restoration.md.

## Proved and sorry left

The restored theorem
AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_sheaves has a complete
proof, including the shorter open-counit subargument. All retained private helpers
are proved. The quarantine baseline has 0 sorry; this delivery closes 0 holes,
adds 0 holes, splits off 0 theorems, and leaves 0 sorry in the item. Restoration
and proof simplification are reported as such, not as a newly closed hole.
Existing dependencies retain their own proof status.

## No longer needed

The proof no longer directly needs
WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs; its private
import and the private helper openUnitIsIso are removed. Nodes
def-sfb-module-open-lower-shriek-adjunction and
def-sfb-module-linear-open-lower-shriek leave this node's proof_deps. The open
counit now uses the already recorded abelian counit declaration attached to
def-sfb-finite-lower-shriek-to-lower-star.

No module is withdrawn. The unchanged public BoundedConstructible import can
still reach module lower shriek transitively; no global module-pruning or hole
reduction is claimed for this local dependency simplification.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine restoration with zero textual holes, not an extant
holed source file. Its absence was not a mathematical withdrawal. The old open
counit argument unnecessarily went through the module extension-by-zero
adjunction and its projection formula; the existing counit-lifting helper works
for both closed and open immersions. The DAG is updated to the shorter argument.
The stock downstream tool cannot inventory the absent live module, so the
change record inventories live and quarantined importers conservatively.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
