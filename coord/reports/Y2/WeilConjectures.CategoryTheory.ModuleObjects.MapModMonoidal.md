## What changed

Completed all ten existing coherence proof fields in
`WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`.
The proofs are the prior landed A4/G4 coequalizer arguments, validated against
the current source. Naturality cancels one relative tensor projection;
associativity cancels two and applies tensorator coherence; unitality uses the
explicit bimodule unitor coequalizer equations and braiding naturality.

The item compiles without warnings through lcompile.py (15.8 seconds).
The unchanged consumers MonoidalModule and UnitCoherence compile against the
repaired sandbox artifact without warnings (11.2 and 28.6 seconds respectively).
Their temporary verification copies are omitted from the delivery.
A programmatic comparison verifies that everything outside the two coherence
proof-field blocks is byte-identical to the library source, including all
signatures, attributes, docstrings, public imports and construction data.
Change record: `coord/changes/Y2-mapmodmonoidal-coherence-proofs.md`.

## Proved and sorry left

Baseline 10 holes; closed 10; added 0; split off 0; remaining 0.
In each of `CategoryTheory.Functor.mapModCoreMonoidal` and
`CategoryTheory.Mod.comapCoreMonoidal`, completed these five proof fields:

- `μIso_hom_natural_left`;
- `μIso_hom_natural_right`;
- `associativity`;
- `left_unitality`;
- `right_unitality`.

No sorry proof remains and no hole is added elsewhere. The six balancing and
linearity lemmas were already proved in the current source and are preserved;
they are not counted as holes closed. The module docstring's historical mention
of sorry is preserved under the source-library boundary.

## No longer needed

None. No import, declaration, module or node is removed. No new import or Sheaf
dependency is needed. The original coequalizer proof route remains intact.
The shortest-route search found the complete prior proofs in landed change
records and reused them; msearch grep found no exact matching abstract theorem. Loogle returned the generic
CoreMonoidal structure and constructors already used by this file. LeanFinder
returned related module and monoid transport constructions, but no exact
coherence theorem replacing these proof fields.
No node has this module as its Lean attachment and the module has no blueprint
tag, so there is no attached node or unit route to update.

## Where the brief, the DAG or earlier work was wrong

The current source contains ten coherence-field holes, rather than the sixteen
holes mentioned in the older G4 repair record. The six theorem proofs already
present are preserved. The assignment can be completed by restoring prior
library proofs without new intermediate statements or definition changes.
No false statement or missing proof dependency was found.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
