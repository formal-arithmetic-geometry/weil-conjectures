## What changed

Completed both constructions in
`Sheaf.CategoryTheory.FilteredHomologyExactCouple` without changing their signatures.
`CategoryTheory.filteredHomologyExactCouple` explicitly supplies the five data fields
from `FilteredHomologyCoupleData` and the six proof fields from
`CategoryTheory.filteredHomologyCouple_exact`. Direct projections from that conjunction
preserve definitional reduction of the data fields.
`CategoryTheory.filteredHomologyEIso` is `eqToIso` of the equality induced by
`-(-p) = p` and `2*p + q - p = p + q`, proved by integer arithmetic.
Change record: `coord/changes/filtered-homology-exact-couple-explicit.md`.
The node's existing one-step proof is followed unchanged; no new route or node is needed.

Validation: the module compiled cleanly through `lcompile.py`; an importing probe
checked that both declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
It also checked by `rfl` that the D/E terms and alpha/f/g maps are exactly the
prescribed explicit data. All five direct consumers were compiled unchanged against
these definitions: FilteredHomologyTowerForwardRepresentatives,
FilteredHomologyTowerDifferential, FilteredHomologyTowerQuotients,
FilteredHomologyCoupleQuotientPages, and FilteredQuotientCanonicalStructure.
All compiled; the first two emit private-module linter warnings. No consumer
adaptation is needed. The required delivery dry run passed as CODEX because the
concrete definition bodies are visible to importers.
The construction uses no witness chosen from an existence
statement. All existing public imports remain public: the exposed definition needs
its exactness theorem to be public too.

## Proved and sorry left

Closed 2 of 2 original holes:
- `CategoryTheory.filteredHomologyExactCouple`
- `CategoryTheory.filteredHomologyEIso`

Both belong to node `def-sp-filtered-homology-exact-couple`.
No holes remain in the item. Added 0 holes; split off 0 statements.

## No longer needed

Removed the redundant proof-only direct import
`WeilConjectures.CategoryTheory.ExactCouple`, already publicly reexported by
`Sheaf.CategoryTheory.ExactCouple`. Its declarations remain needed and available
through that existing import. No dependency nodes or modules were pruned; all three
planned dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The existing exactness theorem already
proves all six equations. An `obtain` elimination of its conjunction in the data-valued
abbreviation obstructs reduction of the E projection; using projections from a local
`let` gives the required explicit transparent construction.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
