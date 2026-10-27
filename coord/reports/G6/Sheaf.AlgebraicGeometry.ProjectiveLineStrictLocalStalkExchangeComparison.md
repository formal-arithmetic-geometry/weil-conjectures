## What changed

Complete the explicit retirement assignment in coord/retire-items.tsv. Withdraw
Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison, whose
smallModel declaration has zero holes. Reattach its existing mathematical node to
AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison in the
adopted WeilConjectures module, recording that theorem's actual proof and two
dependencies. No source-library file, definition or target statement changes.

The sole DAG parent, lem-weil-pbc-p1-strict-local-model-comparison, already imports
and calls the adopted theorem with canonical strictLocalization presentations.
Its dependency remains on the same node. No parent adaptation is needed. The
sk-thm-p1 statement and every realized proof step are retained.

Change record: coord/changes/G6-retire-projective-line-strict-local-stalk-comparison.md.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. This is a duplicate retirement,
not proof-hole progress. The withdrawn declaration
AlgebraicGeometry.Etale.projectiveLine_strictLocal_stalkExchangeComparison_smallModel
was already proved. No sorry remains in a delivered Lean file. The adopted theorem
and its complete proof are preserved verbatim; transitive closure completion is
not claimed.

A complete adapter from the exact small-model statement to the adopted theorem
compiled alone through lcompile.py on the server in 21.2 seconds, exit 0. It composes
eA,eB with Spec of the inverse canonical colimit comparison, proves the structural
identities, transports the compatibility hypotheses, applies the adopted comparison,
and rewrites its conclusion. The adapter was removed rather than retained as another
wrapper. The delivered Lean change is only the withdrawal stub.

## No longer needed

Withdraw one duplicate module:
Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalStalkExchangeComparison.
Its smallModel declaration and six imports disappear with the wrapper. The adopted
replacement retains its original-stalk total-cohomology comparison and strict-local
total-cohomology exchange dependencies; neither mathematical dependency is pruned.

Remove lem-weil-pbc-strict-henselization-small-closed-fiber-comparison from this
node's direct proof dependencies: the adopted theorem takes canonical presentations
and uses no small/full transport. That comparison remains available to its other
consumers. No mathematical node or unit step is removed, and no additional module
is claimed globally pruned.

Source-only downstream.py, full searches of lean/Sheaf and lean/WeilConjectures,
and all quarantine archives find no importer of the Sheaf wrapper or user of its
smallModel declaration. Checking actual dependency fields of every DAG node finds
one parent, already using the adopted theorem. Provenance-only blueprint.from
references are retained. The retirement table's old Sheaf model-comparison consumer
has already been replaced by its adopted implementation.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an open proof obligation; the queue and retirement
list explicitly assign this already sorry-free duplicate for removal. The current
source includes the restoration, smallModel rename and original-stalk-wrapper
retirement. These changes are reconciled; no quarantine archive is deleted.

The small-model and adopted signatures differ in their strict-henselization
presentations. The compiled adapter verifies their equivalence through the proved
structural identity; a name-only substitution would be ill-typed. The actual parent
already supplies canonical presentations, so no extra adapter is needed there.

Fresh msearch.py searches in LeanFinder, Loogle and Mathlib grep found no Mathlib
replacement. Local source search found the adopted comparison. Its composition
through total-space cohomology preserves the original geometric-stalk unit route
and does not invoke a closed-fibre comparison or proper base change circularly.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
