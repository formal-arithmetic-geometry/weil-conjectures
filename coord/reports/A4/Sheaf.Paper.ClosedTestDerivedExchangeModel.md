## What changed

Proved
`AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_derived_exchange_model`
by specializing the existing
`AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.nonaffine_closed_test_exchange_identification`.
Affine source and target provide its quasi-compactness and quasi-separatedness
instances. Its two natural isomorphisms, closed-unit normalization, right-hand
normalization and exchange/restriction equation are retained verbatim; only its
additional shift-compatibility and closed-immersion conclusions are discarded.

Added a proof-only import of that module. Redirected its public import of the affine
theorem module to the existing canonical maps module, removing the resulting import
cycle. This changes one import line in an unclaimed module; every declaration there
is unchanged. Updated the item's node proof, proof dependencies and proof origin.
Change record: `coord/changes/A4-closed-test-affine-specialization.md`.

No new module, definition, theorem, axiom or split statement is introduced. The
specialization is valid also for the zero complex, empty source, I = 0 and I = A:
no additional nonemptiness, nonzero-ring, flatness or properness hypothesis is added.

## Proved and sorry left

Closed 1 of the item's original 3 holes:
`AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_derived_exchange_model`
(node `lem-sfb-closed-test-derived-exchange-model`). Added 0 holes; split off 0 statements.
This is a proof from an existing named theorem whose proof is still pending, as
permitted in stage 3; it does not close the transitive proof of that dependency.

Two original item holes remain unchanged, both on
`lem-sfb-closed-test-derived-exchange-model`:

- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.section_comparison_base_change_naturality`.
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_coefficient_naturality`.

The adapted module retains its two existing holes, unchanged, both on
`lem-sfb-nonaffine-closed-test-exchange-identification`:

- `AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.actual_ambient_exchange`.
- `AlgebraicGeometry.ProEtale.NonaffineClosedTestExchangeIdentification.nonaffine_closed_test_exchange_identification`.

## No longer needed

Removed the import of `Sheaf.Paper.ClosedTestDerivedExchangeModel` from the nonaffine
comparison module, replacing it with `Sheaf.Paper.ClosedTestDerivedExchangeMaps`.
The nonaffine calculation uses only those canonical constructions; it uses no theorem
or coefficient definition from its former importer.

For the final affine comparison, the separate unit-evaluation, K-injective section
model and chain-mate arguments are unnecessary: the already-stated qcqs theorem has
exactly the required normalization conclusions. Removed the three direct proof edges
`lem-sfb-closed-test-unit-evaluation`,
`lem-sfb-closed-test-kinjective-section-models` and
`lem-sfb-closed-test-chain-mate-restriction` from the item's node. These nodes are
not withdrawn: other proofs, including the still-planned geometric and scalar coherence
arguments, may need them. The two unfinished theorem clauses retain their declared
coherence dependencies. No library module is withdrawn or claimed globally pruned.
All other existing imports remain used by the unchanged statements, definitions or
already-proved restriction and test-naturality calculations.

## Where the brief, the DAG or earlier work was wrong

The final affine comparison already occurs as part of an existing stronger theorem
for qcqs sources. Repeating its K-injective construction is unnecessary. Local source
search found that exact theorem; LeanFinder found the general natural-isomorphism
component API, Loogle found no additional specialized result, and Mathlib grep found
only general natural-isomorphism constructors. The specialization uses the project's
existing statement, rather than a newly introduced restatement.

The nonaffine module imported its affine consumer to access canonical maps that now
live in ClosedTestDerivedExchangeMaps. Importing the stronger theorem without
redirecting that import creates a cycle; the original two-file lcompile attempt
reported it explicitly. The import correction preserves every nonaffine declaration
and its proof. There were no existing direct or transitive Lean importers of that
module; the new affine importer is compiled against the corrected module.

Both results express the same closed-test unit/counit calculation from Stacks Tags
09BK, 09BL and 0D6F. This is a specialization used as a tool, not a bypass of any
realized unit statement or proof step; the item's unit has no realized node route
that this specialization removes. No tool_uses approval is added or modified.

The dependency audit additionally found the reverse DAG path from the qcqs node to
the affine model through `lem-sfb-closed-lifted-test-isomorphism-criterion`. The qcqs
node explicitly used only the first, source-independent geometry paragraph of that
aggregate; its later exchange implication is irrelevant. Expanded the aggregate's
first three existing proof steps in the qcqs node, retaining their original geometry,
covering, exact-evaluation and cone arguments with their direct stated dependencies.
The remaining steps and statement are unchanged. Removed its obsolete aggregate
proof edge and tool_uses entry. This prevents the affine specialization from creating
a circular proof plan, without adding any theorem or changing an existing statement.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
