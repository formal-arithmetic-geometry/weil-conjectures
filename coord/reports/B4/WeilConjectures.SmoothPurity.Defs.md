## What changed

Added three completely proved private helpers in
`WeilConjectures.SmoothPurity.Defs`, advancing Steps 6--8 of
`lem-route-smooth-purity-iso-comp-open-immersion`:

- `smoothTrace_realization_transitivity` transports an integral trace-composition
  equation through the specified natural realization comparisons and their actual
  compositor square. The proof uses naturality, not equality detection by reductions.
- `smoothTrace_unit_normalized_transitivity` carries the realized equation through
  the common Tate-source identification and both coefficient-unit isomorphisms.
- `smoothTrace_transitivity_of_realized_traces` instantiates this with the native
  Nagata-built lower-shriek compositor, the live open-unit comparison, and its
  exceptional counit. The normalized trace formulas remain explicit inputs.

Updated that route node's proof text and proof_origin to distinguish these now
proved formal steps from the unresolved geometric construction. No public
signature, definition body, attribute or import changes. No other module changes.
This is partial formalization; the trace-definition defect is not repaired.

## Proved and sorry left

Original holes closed: **0 of 2**. New holes: **0**. Split off: **0**.
The three private declarations above are completely proved.

Both original holes remain, by their full names:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`
  (`lem-route-is-iso-smooth-purity-map`). Its unconditional elaborated signature is
  false; the already proved geometric-point counterexample is retained.
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`
  (`lem-route-smooth-purity-iso-comp-open-immersion`). Formal transport and inversion
  are proved, but the actual normalized geometric trace identification is missing.

The pre-existing dependency hole
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothTrace`
(`lem-route-smooth-trace-representing-unique`) is untouched. Its current uniqueness
predicate omits orientation normalization and has a proved counterexample. None
of the added proofs uses that theorem or derives a result from its inconsistency.
No `sorry` was added or moved and no data were selected from mere existence.

## No longer needed

None. No import, node, module or declaration is removed. The finite, tower,
reconstruction, realization and open-counit dependencies remain necessary for the
unresolved geometric steps; these categorical calculations do not replace them.
The unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The current server queue is a disputed route item with two holes. Its archived
build-error record is an absent buildtree source from 2026-10-27; the current
source exists and is preserved in this delivery.

Two previously certified defects remain: `isIso_smoothPurityMap` omits the
smoothness binder in its elaborated signature, and `existsUnique_smoothTrace`
claims uniqueness from unnormalized Hom bijectivity, which is false even for an
identity map in relative dimension zero. The source boundary has no exception
for changing these adopted declaration/definition bodies or signatures. The
present delivery does not claim to repair them or to close either original hole.
It makes the valid realization and unit-transport steps available without using
those disputed assertions. A proper trace repair still needs a specified,
finite-normalized Hom equivalence, rather than arbitrary representing witnesses.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"WeilConjectures.SmoothPurity.Defs": "b44f184d1f3d1df208a3833b3d0b1d5df73c241a"}, "results": {"Sheaf.Targets.SmoothPurityQbar": {"hash": "b61095f4237cc889a88d12105bb9497ef53983af", "status": "OK"}, "WeilConjectures": {"hash": "a9f1970d653af90a208232c6a0658c40dd10bba9", "status": "OK"}, "WeilConjectures.PoincareDuality.Poincare": {"hash": "24c41d940617dccc117d662fe9a0ea621d946970", "status": "OK"}, "WeilConjectures.TraceFormula.Dualizing": {"hash": "6f0205d1db4c599fd319656d4acc1446b3c84ebb", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T14:13:50+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
