## What changed

Proved `WeilConjectures.finiteHom_ordinary_transpose` from the closed-transpose uniqueness argument and a strictly simpler reduced-evaluation characterization. Added the proof-only import `Sheaf.Paper.FiniteHomOrdinaryTransposeEvaluation`. The new characterization module records the remaining evaluation-coherence argument as one named theorem.

## Proved and sorry left

Closed the `finiteHom_ordinary_transpose` hole. One sorry remains in `WeilConjectures.finiteHom_ordinary_transpose_evaluation`, node `lem-coef-finite-hom-ordinary-transpose-evaluation`; it is the reduced evaluation equation needed to identify the ordinary left-tensor transpose with the normalized right-tensor closed transpose.

## No longer needed

No declared proof dependencies were pruned. The proof uses the existing finite coefficient Hom arrow and internal-adjunction comparison definitions, plus the new characterization node; the previously planned direct use of the exceptional comparison, cochain tensor coherence and internal pairing theorem is recorded by the characterization node.

## Where the brief, the DAG or earlier work was wrong

The original module's public Arrow equality uses the finite etale category instance while the transpose uniqueness calculation elaborates in the underlying derived category. The proof must unfold `finiteHomEtaleCategory` before reusing the Arrow equality. The DAG did not record this category-instance normalization, and the new intermediate node isolates the genuinely mathematical coherence step.

## New nodes

`lem-coef-finite-hom-ordinary-transpose-evaluation` in `dag/nodes/sec-six-functors/lem-coef-finite-hom-ordinary-transpose-evaluation.json` owns the remaining ordinary reduced-evaluation equation and is stated in `lean/Sheaf/Paper/FiniteHomOrdinaryTransposeEvaluation.lean`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteHomOrdinaryTranspose": "0124f7b116c076026caed5b0aac61fcf32fbba49", "Sheaf.Paper.FiniteHomOrdinaryTransposeEvaluation": "8a299fcda6c4fbabf7064344b084773f55ef4f42"}, "results": {"Sheaf.Paper.FiniteHomEtaleIso": {"hash": "8100905c80d2bff9fefd60e890152a13a3efc1d6", "status": "OK"}}, "seconds": 63, "time": "2026-10-28T01:38:25+0800", "transitive": 0, "version": 1}
```

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
