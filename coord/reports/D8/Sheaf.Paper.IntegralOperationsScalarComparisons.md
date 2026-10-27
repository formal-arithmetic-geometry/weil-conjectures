## What changed

Proved `WeilConjectures.scalarOperationsOrdinary_unit`, including its pullback, tensor and
contravariant Hom clauses. The identity specialization of the existing tower law makes
each comparison idempotent after transport through the canonical scalar units.
Naturality and cancellation force that transported comparison to be the identity.
A proved private categorical helper supplies this argument. For Hom, its natural
isomorphism uses the existing `scalarHomOrdinary_isIso` and
`scalarHomOrdinary_naturality`, and the first-variable unit is inverted before taking
opposites.

Added the private proof import `Sheaf.Paper.ScalarExtensionComposition` with `import all`
for its canonical derived scalar composition unit equation. Existing public signatures,
definitions and imports are unchanged. No source-library module is changed.

Searches: LeanFinder, Loogle and Mathlib grep supplied generic natural transformation
extensionality APIs. Local source search identified the canonical
ordinary derived scalar composition unit equations. The unit argument needs no additional
scalar-extension model or new mathematical dependency statement.

## Proved and sorry left

Closed one of the eleven original holes:

- `WeilConjectures.scalarOperationsOrdinary_unit`

Added no holes and no split-off statements. This is a proof from existing declarations,
including the still unfinished tower and Hom-invertibility clauses. Ten original holes
remain, all attached to `lem-pur-integral-operations-scalar-extension` (with the
scalar-completion assertion also attached to `lem-weil-normalized-scalar-completion`):

- `WeilConjectures.scalarPullbackLevel_existsUnique`
- `WeilConjectures.scalarPullbackTower_existsUnique`
- `WeilConjectures.scalarTensorLevel_existsUnique`
- `WeilConjectures.scalarTensorTower_existsUnique`
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`
- `WeilConjectures.scalarTensorOrdinary_existsUnique`
- `WeilConjectures.scalarCompletion_existsUnique`
- `WeilConjectures.scalarOrdinaryTensorChain_existsUnique`
- `WeilConjectures.scalarHomOrdinary_isIso`
- `WeilConjectures.scalarOperationsOrdinary_tower`

## No longer needed

None. No original imports, modules, declarations or planned dependencies are removed.
For the unit clause, the separate pure-generator and Roos-localization calculation is
replaced by cancellation from the already stated tower law. The preceding dependencies
remain needed by the other clauses and their existing proofs or plans.

## Where the brief, the DAG or earlier work was wrong

The latest blueprint defines ambient integral operations directly and explicitly says
that they are not constructions from finite reductions. The assigned module and its DAG
node retain the older completed-operation comparison interface. This delivery preserves
that interface and proves its existing unit assertion without changing any definition
or target meaning. Current blueprint inspected:
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/`
`sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md` and
`sec-six-functors/sk-thm-sf-compatibility/_section.md`.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
