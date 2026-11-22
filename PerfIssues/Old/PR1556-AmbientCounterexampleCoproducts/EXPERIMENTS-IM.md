# Intrinsic vs mismatch-induced DefEq report

Case: PR1556-AmbientCounterexampleCoproducts
Operation family: CategoryStruct.comp -> NatTrans.app
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: final generated congruence proposition domain, NatTrans.app major argument 6.

## Variants and expressions

M is the matched-premise diagnostic in probes/im/MatchedNatTrans.lean. It retains the
same consumer and application pair and reconstructs both major premises through one
provider. O, A, and R are OriginalNatTrans, AlignedNatTrans, and RestoredNatTrans.
The heads are NatTrans.app/NatTrans.app; arguments 0--5 are definitionally equal,
argument 6 is the first non-structural mismatch, and argument 7 is Functor.obj.
The aligned result type is structurally equal and kernel checks.

## Kernel cost

Fresh O counters: 73,189.597 ms, 6,670,198 calls, depth 213,
34,922.251 ms comparison-exclusive, 38,267.345 ms reduction-exclusive,
27,807.890 ms dependent comparison, 7,063.879 ms proposition comparison,
298,357,470 Exprs / 9,970,769,744 bytes, RSS/commit delta 104,923,136 bytes.
The READY2 trace was 142,415.392 ms with 82,161.913/60,253.479 ms
comparison/reduction; 3,428,653 distinct and 1,571,347 repeated pairs cost 565 ms.
The matched diagnostic root was 2,074.191 ms / 284,842 calls. Exact pair checks:
O 67,616 ms, M/A 0 ms, R 70,107 ms. Projection and application branches are
the largest local branches; dependent descendants own the parent.

## Conclusion

H3 with a strong H2 component. The matched premise still performs a nontrivial
kernel check, but the original mismatch adds roughly 67--70 seconds and millions
of calls. No valid independent provider-sharing control preserves the proposition.
unif_hint is not applicable because no relevant inferred provider is present.
