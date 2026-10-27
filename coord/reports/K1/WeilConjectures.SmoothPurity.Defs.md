## What changed

Partial formalization in `WeilConjectures.SmoothPurity.Defs`, with four proved private helpers:

- `smoothTrace_gammaUnit_isIso`: finite orientation at the constructible coefficient unit.
- `smoothTrace_finiteInverseQuotientSquare`: inverse orientation compatibility with every actual root quotient, including equal levels.
- `smoothTrace_reconstructedInverseQuotientSquare`: inverse compatibility with the canonical reductions of the actual derived limit, from `IdentifiesExceptional`.
- `smoothTrace_openComposite_counit`: ordinary open-counit normalization with an arbitrary preceding trace.

The node proof texts record exactly these partial steps. No public signature, definition body, attribute or public import changes. No new data is chosen. No new module or import is added. The original geometric trace construction is still required. These are partial proofs of steps of the existing route, not a completed reduction of an original hole.

Validation: the initial single-file compile passed in 45.2 seconds. The delivery probe
took 60.1 seconds and refused the packet. Three assembly-only helpers were removed
to reduce the additional elaboration; the remaining inverse-square proofs locally
keep their named orientation maps irreducible. The final single-file compile passes in 31.5 seconds without diagnostics; the delivery probe runs next.

## Proved and sorry left

Original holes closed: 0 of 4. New holes added: 0. The four private helpers listed above are complete proofs. This is partial proof work, not a net reduction of the sorry ledger.

All original holes remain, under `AlgebraicGeometry.ProEtale.CondensedRing`:

- `smoothTrace` — `def-route-smooth-trace` (existing hollow definition, unchanged).
- `isIso_smoothPurityMap` — `lem-route-is-iso-smooth-purity-map` (existing disputed unconditional instance, unchanged).
- `smoothPurityIso_zero_of_isOpenImmersion` — `lem-route-smooth-purity-iso-zero-of-is-open-immersion`.
- `smoothPurityIso_comp_openImmersion` — `lem-route-smooth-purity-iso-comp-open-immersion`.

No original hole has been moved under another name. No purity conclusion is derived by exploiting the disputed instance. The ordinary open-counit identity makes no invertibility assumption.

## No longer needed

None. All existing imports, declarations, nodes and unit routes remain needed. There is no withdrawal and no pruning claimed.

## Where the brief, the DAG or earlier work was wrong

The existing `isIso_smoothPurityMap` elaborated signature omits `SmoothOfRelativeDimension d f.left`, although its intended mathematical statement requires it. The existing private separably closed point counterexample certifies that the unconditional statement is false at the identity with d = 1. `coord/upstream-statement-exceptions.tsv` does not authorize correcting this declaration, so this delivery preserves its exact signature and the `STATEMENT-DISPUTED` marker.

The existing `smoothTrace` is still hollow. The declared reconstruction inputs have incompatible native presentations requiring further transport: `ReconstructionResult` packages towers over the lifted Z_ell datum, whereas the condensed exceptional reconstruction and Tate realization use their recorded completed coefficient/system contexts. The new inverse-square theorems preserve the actual root and derived-limit reduction maps; they do not construct that bridge or the trace. Selecting an arbitrary comparison from bare existence would violate the data rule, so no such choice was made.

Searches before the proof: msearch LeanFinder for smooth purity trace/open-composition compatibility returned scheme-open restriction results, not exceptional trace normalization; Loogle found `CategoryTheory.Adjunction.homEquiv_counit`; Mathlib grep found generic adjunction identities and no smooth trace theorem. The existing project helpers and `ReconstructionResult`, `IdentifiesExceptional`, open-unit comparison and their source definitions were read and reused. No shorter geometric trace construction was found.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
