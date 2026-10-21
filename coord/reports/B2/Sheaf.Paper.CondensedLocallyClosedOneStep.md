## What changed

Restored lean/Sheaf/Paper/CondensedLocallyClosedOneStep.lean from the quarantine path
recorded in coord/rework.tsv. Repaired condensed_locallyClosed_one_step by naming the
connecting-map existential hconnect before obtain eliminates it. Direct elimination of the
nested projection failed with `Tactic generalize failed: result is not type correct`.
The theorem's signature, docstring, options, imports and mathematical argument are unchanged.
The repaired single file compiles in 8.1 seconds without errors or warnings.
A subsequent import-order check compiled the final item in 16.4 seconds and its unchanged
archived consumer CondensedLocallyClosedExtensionTower in 5.2 seconds. The consumer copy
is retained only under scratchpad/, outside the delivered Lean files.

The existing node lem-weil-pbc-condensed-locally-closed-one-step keeps its Lean attachment,
statement, proof and dependencies; its proof-origin note records this repair. The unit route
is unchanged. The direct consumer and DAG parent is CondensedLocallyClosedExtensionTower;
its archived proof uses the restored theorem with the same signature.

Change record: coord/changes/B2-restore-condensed-locally-closed-one-step.md.

## Proved and sorry left

This is a zero-hole restoration/repair. The archived declaration
AlgebraicGeometry.ProEtale.condensed_locallyClosed_one_step already had a complete proof;
its repaired proof compiles. Holes closed: 0 of 0. Holes added: 0. Holes left: 0.
There are no split-off statements and no definition changes.

## No longer needed

None. All existing imports are used: CondensedLocallyClosedPiece defines the predicate;
ExactFunctor supplies derived exact-functor operations appearing in the statement;
CondensedConstructibleGenericLfp supplies the nonempty locally finitely presented open;
ProEtaleModuleConstructiblePullback makes the closed restriction constructible;
CondensedOpenClosedRecollement supplies the distinguished triangle and exact closed
pushforward; ProfinitePointPullback supplies the identity coefficient comparisons.
All declared proof dependencies remain needed. No node or module is pruned.

The Mathlib search found finite-presentation sheaf APIs and Triangle.isoMk, but no theorem
replacing this coefficient-generic construction. The existing proof already uses the
triangulated API and the project's proved geometric inputs.

## Where the brief, the DAG or earlier work was wrong

The module is absent from lean/ because it was quarantined, not because its mathematics was
withdrawn. Its rework row is the authority for restoration. The archive has zero sorry
proofs, so restoring it is not a proof-hole closure. Its direct obtain on the deeply nested
connecting-map existential fails against the published build; naming that existential
fixes the elaboration without altering the statement or proof route.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
