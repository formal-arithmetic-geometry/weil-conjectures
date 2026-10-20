## What changed

Restored Sheaf.AlgebraicGeometry.StrictLocalUnderivedSectionsMate from its quarantined
assignment as a public re-export of the existing, proved adopted source module.
This repairs strictLocalUnderivedMateSections: neighbourhood restriction, the exchange
square, global sections, and Q.legs now all use Scheme.strictLocalization and
Scheme.strictLocalizationToBase. The comparison strictLocalUnderivedMateSections_eq
is supplied by the same implementation, under its existing qualified name.

The archive's line-392 and line-441 errors were reproduced with lcompile.py. The restored
module compiles. The exact current adopted implementation is also compiled in a scratch
file with its full comparison type and defining construction equation checked. Both
public names have only propext, Classical.choice and Quot.sound in their axiom lists.
The import-only probe checks name visibility through the restored Sheaf path.

The node keeps its module/file/declaration attachment, mathematical statement, all
statement and proof dependencies, and all proof-step uses. Its proof and proof_origin
record adopted-source reuse; lean.statement uses the canonical model and lean.note
explains this representation repair. No source-library or quarantine file is edited.
The consumer scan reports zero live downstream modules. All three archived/DAG parents
remain recorded; their existing model migrations are independent rework.

Change record: coord/changes/F1-strict-local-underived-sections-mate-source-reuse.md.

## Proved and sorry left

This is an assigned definition repair with zero original sorry holes. Closed: 0 of 0.
Added: 0. Split off: 0. Sorry left in the delivered module: none.

Reused complete proof: AlgebraicGeometry.Etale.strictLocalUnderivedMateSections_eq,
node lem-weil-pbc-strict-local-underived-sections-mate. Its companion definition
AlgebraicGeometry.Etale.strictLocalUnderivedMateSections is actual constructed data.
Both declarations have only the three permitted axioms. This is not claimed as a
new reduction of a proof hole or as positive net hole progress.

## No longer needed

The restored file no longer separately imports
Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm,
WeilConjectures.SixFunctors.BaseChange.Square,
WeilConjectures.AlgebraicGeometry.EtaleObjectSections, or
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence.
The adopted mate module retains the corresponding mathematical dependencies and
its complete six-helper proof. No dependency node or module is pruned, and no
upstream declaration, proof, public import, or attribute is removed.

## Where the brief, the DAG or earlier work was wrong

The archive predates adoption of the canonical strict-local model. Its base-change
construction uses the old model although the restriction transformation and Q.legs
already use the canonical one, so restoring the archived text alone is ill-typed.
The source counterpart supplies a complete coherent implementation; another split
or a new proof chain is unnecessary. There is no mathematical statement correction.

The published compile cache still exposes an old-model mate and comparison despite
having canonical geometry/restriction dependencies. A direct full-signature import
probe therefore detects a model mismatch; compiling the current source implementation
in a scratch file validates the canonical definition and complete proof directly.
The restored import itself compiles, and the delivery/global build must verify the
actual current source dependency set. The quarantine archive is preserved.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
