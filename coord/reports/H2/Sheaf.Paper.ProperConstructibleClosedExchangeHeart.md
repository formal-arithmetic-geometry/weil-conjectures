## What changed

Replaced the sole proof hole of `AlgebraicGeometry.ProEtale.CondensedRing.proper_constructible_closed_exchange_heart` by a Lean assembly of affine descent, constructible pullback and conservative test evaluation. The original theorem signature and public imports are unchanged.

Two intermediate modules isolate distinct parts of the original argument: `Sheaf.Paper.ProperConstructibleLiftedTestRestriction` states invertibility of the exchange after evaluation on one lifted test, including the normalized restriction comparison, and `Sheaf.Paper.CondensedClosedExchangeAffineDescent` states the generic affine descent bridge with no properness, admissibility or constructibility assumptions. Each has a named theorem, a full proof in words and its own DAG node. Both are used in the assembly; neither repeats the global proper constructible exchange conclusion with its original hypotheses.

The proof reuses the source-independent test criterion and finite constant stratified locality. Private, proved `stratified_pullback` is accessed through a proof-only `import all`, without appearing in a public signature or definition. Local irreducibility attributes preserve the existing interfaces during elaboration. Proved private helpers isolate the generic conservative-evaluation application, its inverse-image specialization, constructible pullback, and geometric qcqs permanence. Using the existing `closedMap` abbreviation consistently in both the new descent interface and the affine-chart proof prevents an expensive kernel comparison with its expanded quotient-map expression. No existing definition or source-library declaration is changed.

Validation: `lcompile.py --all` accepted the three final sources individually in 35.9 s, 32.5 s and 39.4 s, with no errors or warnings. The assigned signature and public imports were also compared with the shared source and are byte-identical.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.ProEtale.CondensedRing.proper_constructible_closed_exchange_heart` (node `lem-sfb-proper-constructible-closed-exchange-heart`). There are zero textual holes left in the assigned module.

Added two holes, both entire public named theorem proofs:

- `AlgebraicGeometry.ProEtale.CondensedRing.proper_constructible_lifted_test_restriction`, node `lem-sfb-proper-constructible-lifted-test-restriction`.
- `AlgebraicGeometry.ProEtale.CondensedRing.condensed_closed_exchange_affine_descent`, node `lem-sfb-condensed-closed-exchange-affine-descent`.

This is a decomposition: one upper hole closed and two lower holes added, not a claim of a net reduction in the targets' sorry closure. The single-test lemma still needs the common-closed-fibre rigidity calculation, restriction composition, and conversion to evaluated exchange through the normalized nonaffine comparison. The descent lemma still needs the internal-module transport of ringed open descent.

## No longer needed

No existing public import or module is removed, and no module is withdrawn. No transitive dependency is claimed pruned. The assigned theorem directly needs the two new nodes, `lem-sfb-constructible-zariski-locality`, `lem-sfb-closed-lifted-test-isomorphism-criterion`, and the Mathlib proper/qcqs permanence instances.

The parent node no longer directly cites `lem-pur-scheme-constructible-preimage`, `lem-sfb-scalar-matrix-inverse-image`, `lem-sfb-qcqs-closed-pullback-finite-model-completion`, `lem-sfb-proper-wcontractible-closed-fibre-rigidity`, `lem-weil-pbc-ringed-derived-slice-localization`, `lem-sf-ringed-restriction-exchange-open-descent`, or `lem-sfb-internal-module-operations-transport`: their mathematical roles are recorded on the two intermediate nodes and the proved stratified locality theorem. The normalized nonaffine comparison is likewise a dependency of the single-test intermediate rather than a direct proof import of the assigned module. These declarations remain needed transitively.

## Where the brief, the DAG or earlier work was wrong

The recorded dependency `closed_lifted_test_isomorphism_criterion` requires an affine source, whereas a proper source over an affine base need not be affine. The proof uses the source-independent `closed_lifted_tests_detect_isomorphisms` from the same module. The normalized nonaffine comparison remains part of the single-test obligation. This implements the unit route without the invalid affine-source specialization.

The common-closed-fibre restriction calculation and passage from ringed open descent to the actual condensed mate were described in words but were not present as directly applicable internal-module declarations. They are now explicit, strictly local intermediate obligations. No statement is marked disputed, and no coefficient family, hypothesis or conclusion of the assigned theorem is changed. The assigned theorem's inherited docstring still says six coefficient families; its unchanged statement has the current five-family disjunction.

## New nodes

`lem-sfb-proper-constructible-lifted-test-restriction` is the original plan's single-test calculation: the first three steps followed by the normalized nonaffine exchange identification for that test. Its source is the original closed-complement degree-zero calculation in refinement (2). It leaves conservative evaluation and global affine descent to the proved combination in the assigned module. Its proof plan retains the geometry, scalar-model pullback and proper rigidity dependencies, including zero-ring and empty-scheme edge cases.

`lem-sfb-condensed-closed-exchange-affine-descent` is the generic final affine localization and descent step. It applies to arbitrary condensed coefficients and module sheaves, reducing the global actual mate to its affine quotient chart exact-pullback mates. It uses ringed slice localization, normalized ringed open descent and internal/section-module transport. Both nodes record LeanSearch, LeanFinder, Loogle and local source searches. The additive API record is `coord/changes/H2-proper-closed-exchange-local-interfaces.md`.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
