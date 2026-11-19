Case ID / declaration
---------------------
RealPushforward / `isReal_higherLowerShriek_one`
Origin: `ed3d39ddb5d`; Lean/Mathlib 4.35.0; Weil server the build server.
Imports/options: see `Before.lean`, `maxHeartbeats 200000`.

1. Phase attribution
--------------------
Synchronous Kernel on: 54.73 s / 4,686,328 KB RSS, `(kernel) deterministic timeout`.
Synchronous Kernel skipped: 3.00 s / 3,125,404 KB RSS, exit 0.
Baseline Before/After: 54.94 s timeout / 2.80 s ok. Per-declaration
profiler: type checking 53.8 s, tactic execution 209 ms, elaboration 23.1 ms;
the diagnostic remains `(kernel) deterministic timeout`. Conclusion: Kernel.

2. What is expensive?
---------------------
The target theorem value, at the final `rwa` that rewrites
`FrobeniusModule.localPolynomial` and `Polynomial.coeff_expand_mul` on a
concrete stalk. The type-only control is represented by the cheap After theorem
application to the identical statement; the remaining cost belongs to the old
value or its inferred-type conversion. Exact Kernel suboperation is unresolved.

3. Structural evidence
----------------------
The old proof exposes the concrete stalk's `localPolynomial` definition.
The fix proves `charpolyRev = localPolynomial` for an abstract Frobenius module
and rewrites through that lemma. Hidden instance arguments and shared DAG size
were not dumped; no exact `Expr.equal` result is claimed.

4. Why is it expensive?
-----------------------
Primary A (reduction/definitional equality); contributing E (instance-path
mismatch). Kernel skip is a controlled phase probe; abstract versus concrete
rewrite is a controlled proof-term change. Alternative B remains possible for
the rewrite proof itself. Evidence strength: strongly supported.

5. Confidence
-------------
Strongly supported. A typed-sorry bisect of the final rewrite term could
separate its argument check from final type reconciliation.

6. Scope and caveats
--------------------
Standalone in-situ declaration; diagnostic Kernel skip is not a proof result.
