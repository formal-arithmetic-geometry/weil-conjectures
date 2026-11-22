# Intrinsic vs mismatch-induced DefEq report

Case: PR1624-IntegersSheafHomologyTower
Operation family: dependent Functor.comp endpoints / Iso.trans
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: complete dependent Iso.trans endpoint.

OriginalDependentEndpoint and RestoredDependentEndpoint are O/R; the broad aligned
endpoint is A. M is invalid because replacing one endpoint provider changes later
dependent types. The first divergence is endpoint Functor.comp arguments 2 and 3.

Fresh root 4523: 53,520.575 ms, 6,598,545 calls, depth 88,
26,437.161/27,083.414 ms comparison/reduction, dependent timers
21,452.425/20,539.964 ms, Expr proxy 293,181,229 / 9,796,728,600 bytes,
RSS/commit delta 4,740,874,240 bytes. Trace: 66,439.643 ms,
37,377.645/29,061.999 ms; 3,361,091 distinct and 1,638,909 repeated pairs
cost 672 ms. Isolated endpoint checks were 17,942 and 30,066 ms. A retained
456,393 calls and 5.256 s / 2.557/2.700 s comparison/reduction.

Conclusion: H1/H3; strict M invalid. The endpoint pattern is intrinsically
expensive in context, while alignment removes most mismatch-induced work.
No valid provider-sharing or unif_hint control exists.
