## What changed

Proved `WeilConjectures.zlIndWeilOpenShriek_realization` in
`Sheaf.Paper.WeilIndOpenRealization`, with its signature unchanged. Added only private
proof imports and a proved private helper `zlOpenRealization_commonModel`.

The helper retains the literal output formula in the existing constructive proof of
`commonStageOpenHeartAdjunction`. It reuses that module's proved finite adjunction,
standard-class preservation, invertible-mate and stage-descent helpers. The descended
open left adjoint has the same output objects as any normalized coefficient action S,
by `S.finite_eq`. The main proof restricts this adjunction to hearts, transports it
through AsSmall, extends it to ind-categories, and lifts it to Frobenius fixed pairs.
Uniqueness of left adjoints and fully faithful Yoneda recover the requested carrier
isomorphism. The object equality then identifies its target with the value of S.

Updated the item's DAG proof and dependency list. No other existing module,
definition, statement, shared instance or attribute, or public import was changed.

## Proved and sorry left

Closed the one existing hole in
`WeilConjectures.zlIndWeilOpenShriek_realization`
(`lem-zl-ind-open-realization`). Added zero holes. No sorry remains in this delivery.
`zlOpenRealization_commonModel` is proved, not a split-off obligation.
Existing lower statements retain their independent proof obligations.

## No longer needed

No original import was removed; both public imports are needed by the unchanged
statement. No module is withdrawn.

The proof does not directly use the originally planned nodes
`def-weil-integral-rational-qbar-compact-support`,
`lem-sf-integral-open-reduction-comparison`,
`lem-cbc-completed-extension-zero-comparison`, `sk-lem-sf-open-ctf`, or
`lem-fix-operation-reduction`. Their direct proof-dependency edges are replaced by
the already implemented common-stage open-heart descent and its coefficient-stage
helpers. These nodes can still be needed transitively by those lower results;
no global deletion or claim of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns proof work (one hole). The historical rework record
and build-error file report failed imports through the coefficient-change chain.
The unchanged item compiled against the published artifacts before proof work.
The delivery must additionally pass its server checks against the current sources.
The complete revised proof compiled in 49.0 seconds while profiling. Profiling and
diagnostic commands were removed before delivery; sequential elaboration is retained
to avoid competing elaboration of the two declarations.

The existing common-stage open-heart construction already supplies the necessary
finite adjunctions and descent. Its public existential statement omits the literal
object formula needed here, so the proved private helper reconstructs the same
descent with that formula retained. This only needs the finite functor equality
of S; it needs no new coefficient-action normalization theorem.

The normalized open-unit theorem has a DAG dependency path through its broad
coefficient-exchange route back to compact-support cohomology and this item. The
delivered proof avoids that result and uses only the object formula of open-heart
descent. All added DAG dependency edges have been checked to have no path back to
this item. No existing DAG cycle or unrelated node is modified.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.WeilIndOpenRealization": "20bee50fd34f46d7c0ab05d775c148474b5a3b28"}, "results": {"Sheaf.Paper.WeilCompactSupportCohomology": {"hash": "2bb84ad793dfeab3485f6087a730edf0fc8d33fa", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T00:52:11+0800", "transitive": 0, "version": 1}
```

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
