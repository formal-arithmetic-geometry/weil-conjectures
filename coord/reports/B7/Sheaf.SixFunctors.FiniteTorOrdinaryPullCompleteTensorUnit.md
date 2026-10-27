## What changed

Proved `WeilConjectures.GeneratorReduction.tensorUnit_complete_for_finiteTorOrdinaryPull`
by reusing the already proved private `tensorUnit_complete` from
`Sheaf.SixFunctors.OpenReconstructionEffectivity` through a proof-only `import all`.
The global branch of `IntegralOnSlice.IsComplete` is definitionally the unrestricted
completeness predicate returned by that theorem. The helper constructs the unit
isomorphism using the native K-flat tensor comparison, then transports the existing
completeness of the completed regular coefficient object across it.

Only the assigned module and its own DAG node change. All existing signatures,
definitions, public imports and docstrings are preserved. The node records the native unit identification and constant-object completeness
dependencies of the reused helper, rather than the unrelated public open theorem
in its host module; this avoids a DAG dependency cycle. The import-direction check confirms that the imported module does
not reach the assigned module. The unit's realized statement/steps are untouched.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.GeneratorReduction.tensorUnit_complete_for_finiteTorOrdinaryPull`
(node `lem-sf-finite-tor-ordinary-pull-complete-tensor-unit`).

Server validation: the assigned file compiled cleanly in 3.9 seconds.

One of one holes closed; zero holes added; zero split off; no `sorry` remains in
the delivered Lean file. This reuses a proved helper and is not a decomposition.

## No longer needed

No imports or modules are removed. The two existing public imports still provide
the statement's coefficient calculus and completeness predicate.
`def-weil-derived-complete` remains the statement dependency; it is no longer a
separate direct proof dependency because the existing helper supplies the entire
argument. No new Roos-tower construction, coefficient-unit identification or
completeness lemma needs to be split off or proved for this item. No globally
unneeded module is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier search record missed the proved private `tensorUnit_complete` in
`OpenReconstructionEffectivity`, which already proves exactly the required global
completeness assertion. That module's DAG node describes this argument in its
second proof step. A proof-only `import all`, already used for this helper by
`PrimitiveCompletionEffectivity`, makes the existing theorem available here.
The original plan is mathematically valid but does not need to be reconstructed.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
