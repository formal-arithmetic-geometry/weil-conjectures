## What changed

Restored `Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons`
from the complete quarantine archive named in `coord/rework.tsv`. Removed
`derivedPullback` from the local irreducibility command because the current
upstream declaration is already globally irreducible. The archive reproduces
that command error through `lcompile.py` (48.9 seconds, exit code 1).

A minimal restoration compiled, but a delivery compilation exceeded the
unchanged 60-second file limit. The final proof reduces local row aliases
with projection reduction disabled and uses four proved private helpers. A generic
existential-combination lemma assembles the two comparisons. The denominator
component is calculated for arbitrary short complexes and four functors,
its equality explicitly transports the isomorphism hypothesis with `Eq.mp`, and
`Iso.symm_hom` aligns the square comparison with the one-open lemma.
The existing denominator-isomorphism proofs are passed explicitly. The comparison
and transport proofs are passed directly to the assembly lemmas, avoiding
redundant intermediate proof types.

The public theorem statement, its docstring and all five imports are textually
identical to the archive. The mathematical route remains the middle comparison
plus the one-open comparison for `U ⊓ V`, transported through the prescribed
third-component equation. No data definition, hypothesis or conclusion changes.
No other module is edited and no target or source-library declaration is changed.

The complete refactored proof compiled through `lcompile.py` in 45.5 seconds
under 100000 heartbeats, exit code 0. Profiling measured 4.4 seconds in tactics
and 34.7 seconds in type checking. Diagnostic traces and profiling options are
removed from the packet. The heartbeat budget is reduced from the archive's
1000000 to that verified 100000; the 60-second deadline is unchanged. Delivery
preflight independently recompiles the final packet and performs the axiom probe.

Change record:
`coord/changes/N4-relative-mv-resolved-roof-open-reducibility.md`.
All Lean lines have at most 100 characters. The downstream search reports zero
live downstream modules and theorem uses. The sole archived direct consumer,
`Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofMateComparisons`, applies the
unchanged theorem at lines 242--243 and needs no interface adaptation.

## Proved and sorry left

This is an assigned zero-hole compilation repair. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_resolved_roof_open_mate_comparisons` is fully proved
from the same two imported comparison theorems.
The private helpers `map_third_roof_transport`, `roof_denominator_third`, and
`roof_denominator_transport`, together with `combine_component_comparisons`,
are all proved. No axiom, hollow definition or
unproved intermediate statement is introduced.

## No longer needed

The redundant local irreducibility entry for `derivedPullback` is removed.
The private `component_roof_transport` helper is replaced by the proved component
API above. No import, DAG node or module is pruned. All five imports and the
archived parent's dependency on this theorem are preserved. The parent's absence
from the live tree does not authorize withdrawal.

## Where the brief, the DAG or earlier work was wrong

The operative assignment is the zero-hole restoration in `coord/rework.tsv`.
Its recorded duplicate-import failure has already been resolved by the current
dependencies. The remaining invalid local attribute is the same compatibility
issue encountered by the restored proof dependencies. There is no current
item-specific return in `coord/returns/N4.md`.

Searching `dag/nodes`, `dag/units` and `dag/notes` by module, theorem and blueprint
tag finds no attachment for `lem-pc-relative-mv-resolved-roof-open-mate-comparisons`
in this snapshot. Its archived tag and dependencies are preserved. The same
mathematical proof route is retained; no existing node is changed and no new
public statement or replacement node is introduced.

The required `msearch.py` searches ran: LeanFinder found generic equality
transport results, Loogle found inverse identities, and grep found no live
duplicate of the theorem or its old helper. Direct searches of both library
roots likewise found no replacement comparison theorem.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
