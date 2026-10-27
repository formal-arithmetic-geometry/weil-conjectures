## What changed

Repaired `lean/Sheaf/Paper/CondensedQbarExchangeRightAdjunct.lean`, the timing-repair
item recorded in `coord/rework.tsv`. The original quarantined module had complete
proofs but exceeded the 60-second limit. Its two DAG attachments and all declarations
are retained; this is not a withdrawal or a new decomposition.

The shared source was updated during this session with a focused repair: make the
ambient derived adjunctions, the coefficient comparison, the generic mate
constructions and `restrictFullyFaithful` locally irreducible around the specialized
counit theorem, and apply `lifted_push_counit` directly with its adjunctions inferred
from the goal. Incorporated that repair, removed its local option disabling
transparency checking for types, and wrapped long lines to the 100-character limit.
The final normalization also keeps its six concrete functor, adjunction and
comparison definitions locally irreducible while applying the generic functor-law
lemma, preventing unrelated derived constructions from unfolding during matching.
All mathematical statements, definitions, public imports, instances and exported
attributes are unchanged. The proof route is unchanged, so no DAG edit is needed.

Profiling the original proof with transparency checking enabled took 83.7 seconds,
including 44.1 seconds in its final specialized-counit conversion check. The focused
repair, with transparency checking enabled, compiled in 35.6 seconds; its specialized
counit application took 2.2 seconds. Profiling options are removed from the delivered
source. The existing, previously reviewed premise-suggestion filter is preserved.

## Proved and sorry left

Actual holes in the item: zero. Holes closed: zero; holes added: zero; split off: zero.
This delivery repairs elaboration performance, not a mathematical hole.

The complete proofs of `lifted_push_counit`,
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_push_counit`, and
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_exchange_right_adjunct`
are retained. Their existing DAG attachments are
`lem-weil-pbc-qbar-condensed-push-counit` and
`lem-weil-pbc-qbar-condensed-exchange-right-adjunct`. No `sorry` is left or added.

## No longer needed

None. Both public imports and every mathematical dependency of the existing mate and
naturality argument remain needed. No module, declaration or DAG attachment is
withdrawn. The proof route and unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The missing source at the start was quarantined, not withdrawn. Its rework row records
a 66.6-second compile and zero mathematical holes. Initial attempts to keep only the
derived functors folded did not repair the expensive conversion. The shared source's
more focused adjunction repair does, and its previous transparency-disabling option
is unnecessary.

Lean Finder and Loogle both confirm Mathlib's restricted-counit formula; local source
searches confirm the existing mate cancellation and naturality route. No additional
mathematical statement or split is needed. Public signatures and definitions remain
identical, so no target statement review or downstream adaptation is required.

A direct-consumer check compiled the repaired item, then the unchanged quarantined
`Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` exceeded 60 seconds (reported compile
time 88 seconds). No consumer type error was reported. That module is independently
quarantined; this delivery changes no interface that could force its adaptation.
The final item also compiled in a second consumer check; the unchanged quarantined
`Sheaf.Paper.CondensedQbarExchangeEquality` then exceeded 60 seconds (reported compile
time 77 seconds), with only pre-existing long-line warnings and no type error.
Both unchanged consumer copies were removed after their checks. These timing failures
are reported rather than hidden or delivered as unrelated consumer edits.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
