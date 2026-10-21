## What changed

This is a listed retirement with zero original holes. I withdrew the duplicate
`lean/Sheaf/AlgebraicGeometry/EtaleGlobalSectionsGaloisInvariants.lean` and
updated `lem-sc-etale-global-sections-galois-invariants` to attach to the fully
proved declaration in
`WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants`.
No source-library declaration was modified and no consumer adaptation was
needed because there are no live Sheaf importers.

Validation: the original item compiled in 5.8 seconds. An independent scratch
example with the exact old signature compiles by direct application of the
upstream theorem; `#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound`. `downstream.py` reports zero downstream modules, and a search of
quarantined sources finds no importer or declaration use. The unit record
`sk-thm-br` is preserved.

Change record: `coord/changes/N1-retire-etale-global-sections-galois-invariants.md`.

## Proved and sorry left

Closed 0 of 0 original holes; added 0 holes; split off 0 statements. The
preserved upstream theorem has no `sorry`.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.EtaleGlobalSectionsGaloisInvariants`. Its two
private imports (`WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisInjective`
and `WeilConjectures.AlgebraicGeometry.EtaleGlobalSectionsGaloisImage`) remain used
by the preserved upstream proof, and are not claimed as pruned modules. The mathematical
node and its proof dependencies remain represented by the adopted upstream
theorem. No unit route or target statement is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving a module with `sorry`, but the
current queue and retirement table classify this already-proved duplicate as a
retirement. The upstream theorem supplies the same proposition, with anonymous
implication binders in place of the old named nondependent binders.

Read the existing declarations for `aux-etale-global-sections-injective` and
`aux-etale-global-sections-image`, the unit record and Stacks Tag 04JM. Searches
through msearch.py (LeanFinder, Loogle and grep), followed by direct rg of the
project library, found the exact upstream twin. No new result is needed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
