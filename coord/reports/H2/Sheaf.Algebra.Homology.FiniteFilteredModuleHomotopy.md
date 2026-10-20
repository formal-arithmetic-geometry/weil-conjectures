## What changed

Restored `Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy` from its complete
quarantine archive. Replaced its public import of
`Sheaf.CategoryTheory.FiniteFiltrationInduction` with
`WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension`, whose existing
canonical filtration API supplies the identical named operations needed by the
item. This repairs the reproduced duplicate `IsExhaustive` import failure.
All five declaration bodies, signatures and docstrings are verbatim. The node's
Lean note records the migration; its attachment and dependencies are preserved.

The item compiles cleanly. Four unmodified archived direct consumers also compile
against it: `FilteredQuasiIsoRightCancellation`, `FilteredQuasiIsoRightOre`,
`FilteredQuasiIsoTwoOutOfThree`, and `FilteredQuasiIsoFractions`. No upstream source
file is changed. Change record:
`coord/changes/H2-finite-filtered-module-homotopy-canonical-import.md`.

## Proved and sorry left

Assigned zero-hole restoration and import repair completed. Original holes: 0;
closed: 0; added: 0; split off: 0; remaining in the delivered module: 0.

All five declarations pass `#print axioms` with only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

Preserved declarations:

- `CochainComplex.FiniteFilteredModuleComplex`;
- `CochainComplex.finiteFilteredModuleHomotopyRel`;
- `CochainComplex.FiniteFilteredModuleHomotopy`;
- `CochainComplex.finiteFilteredModuleHomotopyQuotient`;
- `CochainComplex.finiteFilteredModuleQuasiIso`.

## No longer needed

The item no longer imports `Sheaf.CategoryTheory.FiniteFiltrationInduction`;
its existing upstream counterpart supplies the canonical API. No mathematical
DAG dependency, declaration, node or quarantined module is withdrawn. In
particular, `lem-sp-finite-filtration-induction` remains a dependency, supplied by
the existing upstream extension; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

This assignment is a zero-hole quarantine repair, not a missing theorem proof.
The archived import route combines duplicate filtration implementations after the
upstream sync. Its original compilation reproduces the recorded failure; the
single import replacement fixes it. A compilation-only no-op was not delivered.
The live downstream tool cannot discover an absent quarantined module, so the
consumer inventory includes the preserved quarantine archives explicitly.
The queue's 36 quarantined importers are not evidence that this definition is
unnecessary; its attachment, all declarations and all dependencies are retained.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
