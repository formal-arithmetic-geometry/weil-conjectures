## What changed

Filled `WeilConjectures.FiniteExchangeCoherence.identity` and
`WeilConjectures.FiniteExchangeCoherence.compositionIsIso` in the assigned module.
All existing signatures, definitions, public imports, and previously proved theorem bodies
are preserved. New private helpers prove the derived compositor unit equations, the normalized
identity mate, the unique finite-origin realization comparison, and invertibility of the
single-level proper/open mate on an etale antecedent. Private proof imports expose the existing
normalization and composition-factor helpers and finite coefficient transport.

The identity proof uses the actual pullId, ordinarySquare, ordinaryE and ordinaryBeta maps.
The composition proof uses the retained witness and hJ to produce the exact input of
singleLevelFiniteProperOpenTransport; cancellation and the existing generic composition-factor
lemma finish the proof. No new statement with sorry is introduced. The node proof records
these routes and retains the plans for the three unfilled clauses.

## Proved and sorry left

Closed 2 of the original 5 holes:

- `WeilConjectures.FiniteExchangeCoherence.identity`.
- `WeilConjectures.FiniteExchangeCoherence.compositionIsIso`.

Added 0 holes; split off 0 statements. Three original holes remain, each belonging to
`lem-pur-isomorphism-finite-exchange-coherence` and retaining its source and complete proof plan:

- `WeilConjectures.FiniteExchangeCoherence.vertical`.
- `WeilConjectures.FiniteExchangeCoherence.properCoefficient`.
- `WeilConjectures.FiniteExchangeCoherence.openCoefficient`.

The already proved canonicalAgreement, horizontal, and coefficient are unchanged.
compositionIsIso uses the existing named theorem singleLevelFiniteProperOpenTransport,
whose proof is still sorry; this delivery does not claim to close that dependency.

## No longer needed

No existing public import, declaration, node or module is withdrawn. No new holes or
new modules are added to the import closure: the finite coefficient transport modules
were already transitive dependencies. The explored import of CompletedOpenFiniteEtaleOrigins
was removed; its unique associated-module comparison is constructed directly from the
already available pbcAssociatedRestriction_exists and finiteScalarMap_unit.

For identity, the tower-evaluation route is unnecessary: the derived unit laws and the
ordinary open-unit formula suffice. For compositionIsIso, constructing a constant strict
tower, evaluating compositionPastingCoherence, and evaluating its compositors are unnecessary.
The single-level finite proper/open transport lemma gives the central mate directly.
The tower calculus, evaluation, and full composition-pasting dependencies remain in the node
because the unfilled vertical clause still follows that plan. No whole-module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan for composition invertibility passes through
strict towers unnecessarily; the existing single-level transport lemma yields the same
specified map after the explicit finite-origin realization comparison. The last three
clauses are left unchanged rather than replaced by restatements under new names.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
