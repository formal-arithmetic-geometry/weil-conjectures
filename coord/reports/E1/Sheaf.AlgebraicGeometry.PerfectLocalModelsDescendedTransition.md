## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectLocalModelsDescendedTransition.lean`
from the exact quarantine path in `coord/rework.tsv`. Replaced its obsolete
`public import Sheaf.AlgebraicGeometry.DerivedPullback` with
`public import WeilConjectures.AlgebraicGeometry.DerivedPullback`.
The old Sheaf module is an empty withdrawn module. The unmodified archive fails
with five unknown-identifier errors for `derivedPullback`; the replacement publicly
exposes the actual adopted declaration required by the theorem statement.

This is a substantive zero-hole rework repair. All remaining source bytes,
including the theorem statement, complete proof, docstring, local instances,
options and both proof imports, are unchanged from the preserved archive.
The existing DAG attachment and every dependency remain intact; no node edit is
needed because the mathematical argument and statement are unchanged.
Change record: `coord/changes/E1-perfect-local-models-descended-transition-restoration.md`.

The restored item compiled individually through `lcompile.py` without errors or
warnings. A separate importer applied the theorem at its entire verbatim archived
type and printed its axioms: only `propext`, `Classical.choice`, `Quot.sound`.
The direct archived parent applies this same API at line 188. The change record
lists all 36 conservative transitive consumers found by overlaying live sources
on quarantine; no consumer signature or proof requires adaptation to this repair.
The live downstream tool has no consumers while the item and parent are absent.

## Proved and sorry left

The item contains zero `sorry` before and after this repair.
`AlgebraicGeometry.perfect_local_models_descended_transition`
(node `lem-pc-perfect-local-models-descended-transition`) is restored with its
complete existing proof from `perfect_overlap_transition_comparison` and
`TwoOpenComparisonDiagram.realization`.

Holes closed: zero. Holes added: zero. Holes left: zero, including transitive
axioms of the restored theorem as confirmed by `#print axioms`.
No statements are split off, no definitions are changed or added, and no arbitrary
witness is selected from an unproved existence assertion.

## No longer needed

Removed only the obsolete empty-module import
`Sheaf.AlgebraicGeometry.DerivedPullback`, replacing it with the actual public
owner `WeilConjectures.AlgebraicGeometry.DerivedPullback`.
No mathematical node or module is pruned. Both direct proof dependencies and the
statement's canonical Hom restriction API remain required. No archived parent
is withdrawn, and no quarantine archive or existing DAG attachment is removed.

## Where the brief, the DAG or earlier work was wrong

This is the listed zero-hole quarantine repair, rather than an unproved new
statement: its previous proof is complete, but its public import still names the
pre-sync module. The import-only fix is enough to elaborate the unchanged theorem.

LeanFinder returned generic complex and derived-category results, with no shorter
finite-stage overlap theorem. Loogle confirmed `Functor.mapIso` and its API;
local searches identify the existing exact overlap-comparison and realization
lemmas already used by the preserved proof. The source argument in
`literature/stacks-project/perfect.tex`, `lemma-descend-perfect`, descends the
overlap isomorphism before gluing, exactly as this route does. The unit route is
unchanged. No new node or changed theorem statement is justified or necessary.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
