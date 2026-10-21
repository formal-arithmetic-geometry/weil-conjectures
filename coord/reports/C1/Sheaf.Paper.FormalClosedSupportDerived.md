## What changed

Restored Sheaf.Paper.FormalClosedSupportDerived from the exact quarantine path in
coord/rework.tsv. Repaired its two current statement-elaboration errors by deriving
a local colimit-preservation instance from the sheaf adjunction already quantified
in formal_closed_support_derived. No hypothesis or result field is added. The original
complete proof and its four private proved helpers are preserved verbatim.
Updated only the item's Lean statement record and proof explanation to record this
local proof. The unit route, dependency attachments and mathematical statement stay.
Change record: coord/changes/C1-formal-closed-support-derived-restoration.md.

The repaired module compiled cleanly in 18.4 seconds after removing a redundant
private import. Searches through LeanFinder, Loogle, msearch grep and the live library
confirmed the existing uniqueness-of-adjoints route; no new mathematics is needed.
The change record inventories all 185 live-or-quarantined transitive consumers;
no consumer adaptation is required.

## Proved and sorry left

This is a zero-hole restoration and elaboration repair, not a new hole closure.
AlgebraicGeometry.ProEtale.CondensedRing.formal_closed_support_derived retains its
complete proof of the Hom-complex comparison, injective-unit epimorphy, natural
localization triangle with the specified unit/counit, and actual-unit fibre formula.

Holes in the archived module: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No split-off theorem and no new axiom declaration. The axiom probe reports
propext, Classical.choice, Quot.sound and inherited sorryAx from the imported
library chain; the item has no direct sorry. This restoration does not close
those dependency holes. The empty closed/open parts, zero complexes
and unbounded K-injective representatives require no new assumptions: the transport
uses only natural isomorphisms and the recorded exact adjunctions.

## No longer needed

Removed the private import Mathlib.CategoryTheory.Triangulated.Triangulated.
The triangle APIs it supplies are already available through the retained public
support dependency. Both public imports and the other three private imports remain.
No DAG dependency is pruned and no module is withdrawn. The broader support node
and the sheaf-support node remain necessary and keep their Lean attachments.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it was quarantined after a cluster
restore; this does not withdraw the mathematical item. Its archive already has a
complete proof, but its statement assumed an instance that the current public import
context does not provide. The quantified sheaf adjunction supplies that very instance,
so making its proof local repairs elaboration without strengthening the theorem.
The initial archive compile failed at the derived triangle with missing
PreservesFiniteColimits (lowerStar Λ i); the repaired statement compiles.
There is no statement dispute, no new node, and no change to a target definition.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
