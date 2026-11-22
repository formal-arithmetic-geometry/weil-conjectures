# Intrinsic vs mismatch-induced DefEq report

Case: PR1563-RawModuleScalarPullback
Operation family: CategoryStruct.comp / Functor.map
Revision: current-case oleans at a2ec460045b; Lean 4.35.0 READY2.
Root conversion: seven-argument composition in the dependent Eq.mpr domain.

OriginalComposition and RestoredComposition are O/R; AlignedComposition is A. M is
invalid: changing one composition/provider changes the dependent morphism type, so
no non-identical same-obligation matched pair type-checks. First expensive arguments
are Functor.obj (2--4), Functor.map (5), and nested CategoryStruct.comp (6).

Fresh O root 2754: 23,414.588 ms, 2,573,989 calls, depth 95,
11,048.271/12,366.317 ms comparison/reduction, dependent timers
8,899.559/9,767.873 ms. Argument checks were 2,849, 2,467, 2,587, 7,999,
and 25,784 ms. Trace: 28,698.842 ms and 15,785.269/12,913.573 ms; pair sample
1,723,710 distinct, 850,279 repeated, 409 ms repeat-exclusive. Expr proxy
112,996,826 / 3,776,404,760 bytes; RSS/commit delta 54,329,344 bytes.
The aligned construction retained a 20.699 s root.

Conclusion: H1/H3; M is inconclusive by validity. Composition is a path marker;
nested composition, DFunLike.coe, and Functor.map descendants own the time.
No unif_hint or shared-provider control is valid.
