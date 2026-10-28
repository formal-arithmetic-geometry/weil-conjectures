## What changed

Replaced the proof hole in
`WeilConjectures.finitePullbackTensor_ordinary_quotient_square_pure` without changing
its statement. The proof uses the existing homogeneous pure-tensor extensionality
lemma and total-tensor generator map formula, together with the supplied four
generator normalizations, `hc`, and `hcc`. Private proved helpers express the
quotient-unit normalization and naturality, pullback-unit naturality, section
transports, and the elementary function-diagram calculation. The generator proof
holds the quotient calculus abstract, then specializes to the prescribed calculus.
The proof imports `Sheaf.Algebra.Homology.ScalarHomTensorCoherence` and
`Sheaf.Paper.CoefficientTotalTensorMapGenerators` privately.

The item's node now records the actual unit calculation and its dependencies.
No other existing module, public definition, instance, or statement is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finitePullbackTensor_ordinary_quotient_square_pure`
(node `lem-pur-finite-pullback-tensor-ordinary-quotient-square-pure`).
Added zero holes. No `sorry` remains in this module or is added elsewhere.
This is a proof, not a decomposition into new obligations.

Validation: `lcompile.py` compiled the final module cleanly, without warnings,
in 38.6 seconds, below the 60-second limit. The original theorem signature was
also compared verbatim against the shared source.

## No longer needed

None. No original import, planned dependency, module, or node is pruned.
No new proof obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The previous one-step proof plan is
expanded into the actual generator calculation. Scalar restriction and direct
image preserve underlying sections but change their module types; explicit
section transports and naturality equations keep these type comparisons small.
In particular, proving scalar-restriction section injectivity with abstract rings
avoids kernel unfolding of the concrete quotient-ring constructions. The complete
proof compiles within the per-file time limit after this change.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquarePure": "6773aa36669e6ff79d368818fa2d5ca856444e91"}, "results": {"Sheaf.Paper.FinitePullbackTensorOrdinaryQuotientSquareComponent": {"hash": "0c191148e6f8754a4187488a25e4a4b72245588d", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T13:04:05+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
