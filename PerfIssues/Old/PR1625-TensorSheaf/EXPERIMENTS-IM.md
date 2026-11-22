# Intrinsic vs mismatch-induced DefEq report

Case: PR1625-TensorSheaf
Operation family: nested CategoryStruct.comp -> NatTrans.app
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: leftDerivedUpperStarTensorComparison_app_app_fac final dependent equality.

M/O/A/R are MatchedNestedApp, OriginalNestedApp, AlignedNestedApp, and RestoredNestedApp.
All retain the outer and inner applications and the dependent result type. The first
structural divergence is the outer NatTrans.app major argument 6; the inner app and
CategoryStruct.comp descendants remain in the consumer.

Fresh O counters: 114,240.281 ms, 11,757,788 calls, depth 125,
59,140.866/55,099.415 ms comparison/reduction, dependent timers
45,167.426/45,028.549 ms, Expr proxy 438,450,718 / 14,677,924,016 bytes,
RSS/commit delta 5,295,898,624 bytes. The READY2 trace was 142,415.392 ms
with 82,161.913/60,253.479 ms comparison/reduction; 3,284,552 distinct and
1,715,448 repeated pairs cost 377 ms. Exact application checks were O 111,474 ms,
M/A 0 ms, and R 109,892 ms. Top descendants were CategoryStruct.comp (1.003 s),
NatTrans.app (542 ms), NSMul.proj (473 ms), AddGroup.proj (472 ms), and Functor.obj
(242 ms).

Conclusion: H3 approaching H2. A matched application pair is cheap, while O/R are
about 110 seconds; the inner application remains expensive in isolation, so this
is an interaction between intrinsic nesting and the mismatched outer premise.
No valid shared-provider or unif_hint control preserves the dependent telescope.
