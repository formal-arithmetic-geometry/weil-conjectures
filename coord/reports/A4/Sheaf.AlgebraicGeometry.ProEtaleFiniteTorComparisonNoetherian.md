## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteTorComparisonNoetherian.lean`
from the quarantine path recorded in `coord/rework.tsv`. The active module is absent
following the merge queue's cluster restore rollback. Its preserved source already
contains the complete proof of
`AlgebraicGeometry.ProEtale.finiteTorComparisonNoetherian`, together with the proved
private helpers `coefficientTor_iso` and `restrictComparison`.

The archived source compiles unchanged against the current library using `lcompile.py`
(exit 0, 7.1 seconds, no warnings). Its flat-model, flat-pullback and tensor-test-reflection
dependencies are now present. This delivery restores the missing theorem; it does not
change a definition, a signature, an attribute, a public import, or the proof route.
The existing Lean attachment and all node dependencies remain in place.

Reviewed the four proof dependencies and their actual Lean interfaces. The proof obtains
the canonical functor and bounded constructible equivalence from `constructibleComparison`,
uses the flat-model criterion to preserve each exact Tor interval, reflects tensor-test
vanishing using a flat K-flat representative, and restricts the equivalence by the proved
isomorphism-invariance and full-subcategory arguments. This keeps the unit's prescribed
constructible-comparison route. No antecedent with arbitrarily chosen mathematical data
is introduced by the restoration.

## Proved and sorry left

The quarantined baseline has zero local holes; the restored module has zero local holes.
Holes closed in this repair: 0 of 0. Holes added: 0. Split off: 0.

`AlgebraicGeometry.ProEtale.finiteTorComparisonNoetherian` and both private helpers are
proved. No `sorry` remains in any delivered declaration. The original historical hole
was closed by J9 before quarantine; this restoration does not claim that closure again.
The proof still uses the existing declared comparison results, including the pre-existing
unfinished `constructibleComparison`; no claim of an entirely sorry-free transitive
closure is made.

## No longer needed

None. All imports, node dependencies, and the unit route of the archived proof are retained.
No module or node is withdrawn. The three direct private proof imports supply the flat-model
criterion, flat pullback and K-flat transport, and single-test vanishing reflection.

Searched the library by the Tor predicate and comparison theorem names, and used msearch
Loogle and LeanFinder for restriction of equivalences to full subcategories. Mathlib's
`Equivalence.congrFullSubcategory` is a generic related result; it does not replace either
Tor implication or directly identify the nested full subcategories with the required
ambient functor. The existing complete private restriction proof remains appropriate.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief suggests an open local proof hole. The current rework row instead
records a missing module after the cluster restore rollback. The archive is already proved
and compiles with the current dependencies, so restoring it is the assigned repair.
There is no mathematical statement correction and no new DAG node. The existing node's
statement, Lean attachment, proof, proof dependencies and unit route agree with the source
and are preserved.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
