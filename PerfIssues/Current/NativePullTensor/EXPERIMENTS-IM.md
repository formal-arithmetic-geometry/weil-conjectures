# Intrinsic vs mismatch-induced DefEq report

Case: NativePullTensor
Operation family: Functor.obj / Functor.map
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: the two Exists.choose application domains under the original telescope.

OriginalRoot and RestoredRoot preserve O/R. MatchedFunctorObj constructs regular
provider wrappers on both sides; MajorAlignment supplies A and checks a structurally
equal replacement type. The first divergence is Functor.obj provider argument 4.

Fresh O counters: 22,804.855 ms, 2,685,580 calls, depth 81,
15,349.294/7,455.561 ms comparison/reduction, dependent timers
10,288.544/5,580.792 ms, Expr proxy 97,609,480 / 3,325,394,512 bytes,
RSS/commit delta 1,812,267,008 bytes. Trace: 41,488.973 ms,
22,845/18,644 ms; 842,601 distinct and 1,842,979 repeated pairs cost
2.230 s. Exact endpoint checks were O 14,310/13,881 ms, matched regular 1 ms,
matched abbrev 14,134 ms, and A 0 ms.

Conclusion: H2 for the provider mismatch with residual H1/H3 context cost. A
non-identical matched regular pair is effectively free, while O and the abbrev
provider are about 14 seconds. No genuine implicit assignment was found:
unif_hint U0/U1 are unavailable and no Kernel optimization claim is made.
