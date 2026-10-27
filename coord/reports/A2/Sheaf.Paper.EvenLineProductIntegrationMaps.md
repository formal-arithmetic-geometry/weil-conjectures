## What changed

Restored `lean/Sheaf/Paper/EvenLineProductIntegrationMaps.lean` from its current
quarantine archive, retaining all declarations and dependencies. Repaired the
private `ordinaryLine_ctf` proof by unfolding only `Etale.ordinaryFiniteDegreeZero`.
The current definition directly applies `DerivedCategory.singleFunctor`; it no
longer contains `Etale.ordinaryFiniteSingleFunctor`. Asking `unfold` to expand that
absent constant was the recorded build failure at line 353.

The repaired proof retains the existing finite-etale-line construction,
constructibility argument, flatness bound and shift argument. All public
signatures, definitions, attributes and imports are verbatim those of the archive.
No other existing module or node is changed; no change record or consumer
adaptation is needed for this proof-only repair. The node's attachment and proof
plan remain valid.

Validation: `lcompile.py` compiled the repaired complete module without errors or
warnings in 52.2 seconds, within the 60-second per-file limit.

## Proved and sorry left

Assigned compile repair: `ordinaryLine_ctf`, under node
`def-pur-even-line-product-maps`. Original holes: zero. Holes closed: zero of zero.
Holes added: zero. Remaining holes: none. Split-off statements: none.
The module's existing public theorems `block_geometry`, `external_origin`,
`coordinate_geometry`, `coordinate_origins` and `projection_isIso` retain their
complete proofs. This delivery claims a compile repair, not new hole closure.

## No longer needed

None. No imports, declarations, modules or DAG dependencies are removed.
Only the obsolete `Etale.ordinaryFiniteSingleFunctor` argument to one `unfold`
tactic is removed. The archived module is restored rather than withdrawn, and
the unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The archived proof expected `ordinaryFiniteDegreeZero` to be implemented using
the cached single functor. The current source instead defines its object directly
with the native single functor and uses that object in the cached functor. This
makes the extra unfold fail, without changing the mathematical argument.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
