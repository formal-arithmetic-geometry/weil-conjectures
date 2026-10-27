## What changed

Restored the recovered proofs of all three upstream finite-hypercover descent
clauses on top of the current source. All current public imports, signatures,
attributes, copyright and declaration docstrings of the upstream item remain
unchanged. The mathematical argument and the unit route follow the existing DAG.

Repaired the returned duplicate-statement failure by reusing the 39 existing
private helpers in
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`
with a private `import all`, instead of copying their declarations. That helper
module drops its unused public import of the item to avoid an import cycle.
Every helper declaration and proof stays verbatim. Its sole existing direct
consumer, `Sheaf.AlgebraicGeometry.GrothendieckHypercoverSectionColimit`, adds a
direct public import of the item to preserve its previous public import closure;
its declarations and proofs stay verbatim. Both adapted Sheaf modules were
unclaimed. The change record is
`coord/changes/finite-hypercover-descent-reuse-helpers.md`.

No new public declarations, helper statements, nodes or modules are added.

## Proved and sorry left

Closed all three original holes:

- `AlgebraicGeometry.finite_hypercover_descent_objects`
  (`lemma-weil-pbc-finite-hypercover-descent-objects`).
- `AlgebraicGeometry.finite_hypercover_descent_morphisms`
  (`lemma-weil-pbc-finite-hypercover-descent-morphisms`).
- `AlgebraicGeometry.finite_hypercover_descent_equalities`
  (`lemma-weil-pbc-finite-hypercover-descent-equalities`).

Zero holes remain in the item; zero holes added or split off. Both accompanying
Sheaf modules have zero holes. All reused helpers have complete proofs.
Validation: the extracted helper module compiled in 28.7 seconds and the
restored upstream item in 18.3 seconds, without errors or warnings. Source-level
checks confirm identical upstream theorem statements and public imports. The
section-colimit consumer compiled in 6.9 seconds against both repaired sandbox
modules, without errors or warnings. Final delivery preflight is run by deliver3.py.

## No longer needed

Removed all 39 copied helper declarations from the returned packet: their existing
private declarations in the extracted helper module are reused. Removed the
packet's direct private proof imports of
`WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent`,
`Sheaf.Paper.TruncatedFiniteSplitEtaleDiagram`,
`WeilConjectures.AlgebraicGeometry.DescendSurjective`,
`Mathlib.CategoryTheory.Presentable.Directed`, and
`WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs`; the reused helper
module already provides them.

Removed the unused import of the upstream item from the helper module, reversing
the dependency. The section-colimit module imports the item directly so no
existing downstream declaration is lost. No original upstream public import was
removed. No mathematical nodes or modules are pruned: the existing proof
requirements still implement the argument.

## Where the brief, the DAG or earlier work was wrong

The earlier packet incorrectly copied the helper declarations despite their
existing extracted versions. The landing check correctly detected duplicated
statements. Contrary to that packet's report, private visibility does not prevent
reuse here: `import all` is the established mechanism, also already used by the
section-colimit consumer. The extracted helper module's unused dependency on the
upstream item was the only cycle to remove.

Maintainer follow-up requested by the assignment: register the upstream proof
import
`Sheaf.UpstreamExtra.WeilConjectures.AlgebraicGeometry.FiniteHypercoverDescentParts`
(including its `import all` form) in coord/upstream-statement-exceptions.tsv so
future upstream syncs preserve the restored proofs. No private helper needs to
be restored in the upstream file. This delivery does not edit the maintainer's
table.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
