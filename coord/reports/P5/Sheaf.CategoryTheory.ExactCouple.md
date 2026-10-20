## What changed

Retired `Sheaf.CategoryTheory.ExactCouple`, whose only three declarations duplicate
`CategoryTheory.BigradedExactCouple.derived_alpha`, `derived_f`, and `derived_g` in
`WeilConjectures.CategoryTheory.ExactCoupleExtension`. Their types, proofs and simp
attributes match verbatim. `deleted.txt` withdraws the redundant module. Its two direct
importers, `Sheaf.CategoryTheory.FilteredHomologyExactCouple` and
`Sheaf.AlgebraicGeometry.TruncationExchangeCouple`, now publicly import the upstream
extension directly. Both were unclaimed. Only their import lines change; no
source-library file or mathematical declaration changes.

The two modified direct consumers compile without warnings through lcompile.py
(6.2 and 1.4 seconds). All ten transitive consumers also compiled against the upstream
extension re-export (1.1–6.6 seconds per consumer). The final overlay with both
direct import edits also compiles all ten successfully (1.2–6.6 seconds for the
eight indirect consumers). The unchanged `TruncationExchangeAbutment` and
`FiniteRangeComparison` emit their existing private-module visibility warnings.
Unchanged consumer copies used for validation are not delivered.
The import-direction check allows the new import. Mathlib searches through msearch.py
(LeanFinder, Loogle, grep) found no corresponding exact-couple API; local source search
found the exact upstream declarations. No new mathematical result or node is needed.
A temporary axiom probe compiled against the re-export confirms that all three
simp lemmas and `derivedMaps_exists` use only `propext`, `Classical.choice`, and
`Quot.sound`; the probe was removed from the delivered file. A byte-for-byte
comparison confirms that the old three declarations occur verbatim upstream.

Change record: `coord/changes/exact-couple-upstream-simp-reexport.md`.
The node `def-sp-exact-couple` already names the original upstream structure and derived
couple, so its statement, proof route, dependencies and Lean attachment need no change.

## Proved and sorry left

The assigned module had zero `sorry` before this delivery and is now withdrawn.
The adapted consumers also have zero `sorry`; none is added anywhere.
Holes closed: none (0 of 0). Holes added: none. Split off: none. The three already
proved projection identities now resolve to their existing upstream declarations.
This is duplicate retirement, not a newly proved theorem or decomposition.

## No longer needed

The local declarations `CategoryTheory.BigradedExactCouple.derived_alpha`, `derived_f`,
and `derived_g` are removed in favor of their identical upstream declarations.
The direct private import `WeilConjectures.CategoryTheory.DerivedCoupleMapExactness`
is removed with the withdrawn module. Its direct public import
`WeilConjectures.CategoryTheory.ExactCouple` is replaced by the extension import,
which re-exports it. Neither upstream module is globally pruned: the upstream
existence proof still uses the map construction and exactness results.
Pruned module: `Sheaf.CategoryTheory.ExactCouple`. No DAG node or source-library
declaration is withdrawn; the node remains attached to the upstream structure.

## Where the brief, the DAG or earlier work was wrong

The dispatched item has no remaining holes in the current shared source. The
2026-10-20 retirement inventory marked it DIFFERENT because the upstream base
`ExactCouple` lacks the three simp lemmas; all three are actually present verbatim
in upstream `ExactCoupleExtension`. Redirecting its consumers removes this duplicate
without changing the mathematical statements. No defect in the DAG's mathematics
was found, and its unit route is preserved.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
