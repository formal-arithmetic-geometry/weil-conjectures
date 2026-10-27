## What changed

Repair the dangling Lean attachment of
`lem-weil-pbc-unrestricted-strict-henselization-stalk`: it currently names a
declaration in the already empty, withdrawn item module. Attach it to the existing
adopted `AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk` in
`WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`, recording
its exact current signature and `existing = true`.

Reconcile the explicit `coord/retire-items.tsv` assignment by keeping the duplicate
withdrawn through `deleted.txt`. This is substantive metadata repair: the node now
resolves to an actual declaration. No Lean definition, theorem, target or consumer
signature changes. Change record:
`coord/changes/M4-unrestricted-strict-henselization-stalk-retirement.md`.

The adopted theorem uses `strictLocalization`, while the old record used the
small coordinate-ring colimit scheme. They are canonically isomorphic over the
base, not definitionally equal. Existing consumers already import the adopted
theorem, and consumers needing the small model already transport explicitly.
The separate `smallModel_isIso_strictHenselizationCohomologyComparison` theorem,
its module and its node are retained verbatim. All mathematical DAG dependencies
and the unit route remain intact.

## Proved and sorry left

Zero holes in the assigned live module before or after this repair: proved 0 of 0;
holes closed: none; holes added: none; split off: none. The module contains no
remaining declaration or sorry. No other Lean module is changed or added.
The adopted unrestricted stalk theorem already has a complete proof assembling
existence of the canonical germ restriction and the two isomorphism results.
Reusing it is the requested shortest route; this delivery claims no new theorem proof.

## No longer needed

The duplicate `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk` is
already an empty withdrawn module. Its obsolete declaration attachment is removed
in favor of the actual adopted declaration. This repair introduces no additional
module pruning and removes no live import. Zero live importers and declaration
users were confirmed with `tools/downstream.py --uses` and source searches.

Every direct DAG parent was also checked: their references are to the mathematical
unrestricted stalk formula and remain intact. This is reconciliation with the
explicit retirement assignment, not an inference of irrelevance from zero imports.
No DAG node, statement/proof dependency, tool-use approval, small-model theorem,
archive, unit or chapter is removed. No new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The brief assumes a live module containing sorry or an assigned repair. In fact
the item source is already a two-line withdrawn stub with zero holes, and its
rework was marked done on 2026-10-21. The still-listed retirement and stale DAG
attachment explain the residual assignment. Restoring the old declaration under
its original name would collide with the existing adopted theorem. Merely
copying the empty module would leave the actual attachment defect unfixed.

The adopted and small-model schemes must not be substituted by definitional
conversion. Their canonical comparison is already available, and the existing
small-model comparison is preserved. The original node statement and all of its
dependencies are unchanged; only the Lean realization is reconciled.

Mathlib searches via the required search tool found only topological stalk and
structure-sheaf results (Lean Finder), functor-preservation of isomorphisms
(Loogle), and no strict-henselization stalk result (grep). The exact general
result is already in the adopted source library.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
