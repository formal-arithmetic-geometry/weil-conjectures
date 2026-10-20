## What changed
Withdrew the duplicate `lean/Sheaf/AlgebraicGeometry/StrictHenselizationClosedFiber.lean`.
The two consumers now import `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`
and call its proved `strictHenselizationStructuralMap_fiber_eq_closedPoint_compat` theorem.
The closed-fibre DAG nodes now attach to the official upstream strict-localization declarations.
Change record: `coord/changes/D5-strict-henselization-closed-fiber-retirement.md`.
The current `coord/retire-items.tsv` row and the human hand-off in
`coord/changes/retire-sheaf-twins-20261020.md` authorize this zero-hole retirement.

## Proved and sorry left
Holes closed: 0 of 0. Holes added or split off: 0. No `sorry` remains in any delivered Lean
source. The removed declarations are
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_closedPoint_eq` and
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint`; their exact
full-model counterparts remain proved upstream. This is retirement, not a new proof or
decomposition. Both adapted consumers compile with unchanged public theorem signatures.
The comparison module, copied unchanged only because its published object file was initially
missing, also compiles. The delivery tool compiled all three with its axiom/sorry probe.

## No longer needed
Pruned module: `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber`. Its two node
attachments remain on the official upstream theorems, so no mathematical result or unit step
is removed. Each adapted parent node now names
`lem-weil-pbc-strict-henselization-small-closed-fiber-comparison` in place of
`lem-weil-pbc-strict-henselization-closed-fiber`. The latter node remains needed by the official
core-completion theorem.
The duplicate Sheaf closed-fibre module and its `Sheaf.Paper.StrictHenselizationFunctoriality`
proof import are no longer needed. The old direct dependency on the duplicate singleton-fibre
module is replaced by the canonical small-to-full comparison theorem.

## Where the brief, the DAG or earlier work was wrong
The generic proof brief does not identify the retirement assignment: the current queue lists
this zero-hole module as a retirement item, and its upstream strict-localization twin is proved. The retirement record correctly identifies the twin as the
source of truth, but the remaining small-model consumers needed the existing comparison theorem;
this delivery makes that API migration explicit.

## Forced adaptations
Both consumers were unclaimed when edited. The original consumer files imported the withdrawn
duplicate module and applied its equivalence
under the small-model `strictHenselizationScheme` presentation. After withdrawal those imports
and calls fail because the upstream theorem uses `strictLocalization`. The changed lines replace
the import and apply the already proved comparison compatibility theorem, which has the exact
small-model hypotheses and conclusion. No public signatures changed.
In `StrictHenselizationModuleFibreFactorization.lean`, the necessary edits are the private import
at line 14 and the forward call at lines 156–158. In `IntegralFibreSectionLocalLiftAux.lean`,
they are the private import at line 8 and the forward call at lines 99–101.
The withdrawal makes the old imported declaration unavailable; the existing comparison theorem
has exactly the implication each call needs. No other proof lines are changed.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
