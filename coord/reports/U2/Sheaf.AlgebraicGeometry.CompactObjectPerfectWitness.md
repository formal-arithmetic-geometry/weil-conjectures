## What changed

Restored Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness from the current
quarantine archive named by coord/rework.tsv. Replaced the obsolete public import
Sheaf.CategoryTheory.CompactObject with
WeilConjectures.CategoryTheory.CompactObject, which now owns the public definition
CategoryTheory.IsCompactObject. Every other line, including the full theorem
statement and proof, is unchanged from the archive. No source-library files change.
Change record: coord/changes/U2-compact-object-perfect-witness-import.md.

The repaired module compiles through lcompile.py in 2.5 seconds. A separate importing
probe and the repaired module compile together through lcompile.py --all (2.8 and
1.5 seconds). The probe checks that both the theorem and IsCompactObject are public
and prints the theorem's axioms: exactly propext, Classical.choice and Quot.sound.
The temporary probe is excluded from the delivery. Searches of lean/ and quarantine/
find no current Lean consumers requiring adaptation. The DAG's parent dependency is
preserved, along with the item's attachment, two proof dependencies and unit route.

## Proved and sorry left

This is a zero-hole compilation repair, not new mathematical proof progress.
AlgebraicGeometry.compactObject_perfect_witness
(node lem-sc-compact-object-perfect-witness) retains its complete proof from
AlgebraicGeometry.noetherian_open_derived_categories_exists and
AlgebraicGeometry.compact_isPerfect_of_isNoetherian. Both dependency signatures were
checked against their DAG attachments. Holes before: 0. Holes closed: 0 of 0.
Holes added: 0. Holes left: 0. Split off: 0. No definitions or axioms are added.

## No longer needed

The direct import Sheaf.CategoryTheory.CompactObject is obsolete: that compatibility
module has been withdrawn and contains no declarations. Its replacement imports the
adopted source definition publicly. No mathematical nodes or modules are pruned from
the dependency route. All other imports and both declared proof dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The item is assigned quarantined rework and already has zero holes. Its original
quarantine diagnostic records a duplicate IsCompactObject declaration during the
source sync. In the current library the duplicate Sheaf definition is already
withdrawn. Compiling the unmodified archive therefore instead reports that
IsCompactObject is known only through a private import and explicitly requests
public import WeilConjectures.CategoryTheory.CompactObject. The replacement fixes
that current reproducible error without changing the proof or mathematical meaning.

The U2 return file contains only the historical 2026-10-15 upstream-sync notice;
the packet was reconstructed from the current quarantine source, not an old return.
The archive is neither deleted nor modified. No false statement or missing lemma was
found. Mathlib searches (LeanFinder, Loogle and grep) gave no shorter specialized
result; the existing two-result proof is retained unchanged. No second-reader section
is claimed; delivery supplies the independent review.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
