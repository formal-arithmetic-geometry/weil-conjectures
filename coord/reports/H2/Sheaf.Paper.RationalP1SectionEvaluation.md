## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation`
from the existing `first_section_tensor_evaluation_core`. A proved private categorical
helper appends the terminal tensor-unit comparison and right unitor using functoriality,
tensor functoriality and associativity. All existing definitions, mathematical signatures,
attributes and public imports are preserved.

The native instance expressions require explicit congruence proofs to avoid an expensive
kernel conversion. The private proof procedure adapts the existing procedure in
`Sheaf.Paper.FiniteCoefficientProperFormulaTools` (G3), adding backtracking for wrappers
whose argumentwise comparison fails before unfolding. It constructs ordinary equality
proofs using reflexivity, proof irrelevance, function extensionality and congruence.
Lean checks those proofs in its kernel. The final file compiled without warnings in
43 seconds and again in 51 seconds during the consumer check. The four direct importers
`RationalP1FirstTraceTransport`, `RationalP1FirstTraceTransportCore`,
`RationalP1FirstTraceTransportCounit` and `RationalP1UnitFactorization`, and the indirect
user `RationalP1FirstAmbientContraction`, all compiled unchanged, taking 13 to 26 seconds
each. Their temporary sandbox copies were removed. Only proof imports were added:
`Mathlib.Logic.Function.Basic` and `Mathlib.Lean.Meta.CongrTheorems`. Reducibility attributes
used by the procedure are local, and its elaborator syntax is local.

Updated the terminal node to record its actual use of the existing core lemma. Replaced
the core node's statement dependency on the terminal theorem by the definitions of their
common setting, preventing a dependency cycle. Its statement, Lean signature and planned
proof stay unchanged. The change record is
`coord/changes/H2-section-evaluation-core-setting-dependencies.md`.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation`
(node `lem-sfb-rational-p1-section-evaluation`).

One existing hole remains:
`AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation_core`
(node `lem-sfb-rational-p1-section-evaluation-core`). Its statement and `sorry` body
are untouched. The terminal theorem still depends on this admitted core calculation.

The current server source and queue contain two holes; the first local snapshot had
one. This delivery closes one of those two and adds zero holes. The private lemmas
`finish_tensor_evaluation` and `coefficientPiEq` are fully proved. No statements were
split off, no data were chosen from an existence statement, and no definition was changed.

## No longer needed

No modules or imports are withdrawn. The terminal theorem no longer directly uses the
seven previous proof dependencies: `lem-sfb-ringed-projection-tensor-composition`,
`lem-pd-module-ringed-topos-derived-comparison`,
`def-sfb-internal-diagonal-tensor-comparison`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`,
`def-sfb-projective-diagonal-composition`, `def-sfb-projective-diagonal-pullback`,
and `def-sfb-diagonal-coefficient-category`. Their relevant obligations remain in the
existing core lemma and its setting; this is no claim to prune them from the library.
The terminal theorem now directly uses `lem-sfb-rational-p1-section-evaluation-core`.

## Where the brief, the DAG or earlier work was wrong

The shared source changed during the initial read. A targeted server read confirmed the
already landed core lemma, absent from the first snapshot. The earlier delivery added
that lemma but left both it and the terminal theorem admitted. The terminal normalization
can be proved without another split.

Direct normalization of concrete derived module expressions exceeded the kernel budget.
The differing expressions include the direct sheaf tensor instance and its Grothendieck
sheaf presentation, and automatically extracted instance proofs. Applying a categorical
normalization and explicitly proving the expression congruences resolves the conversion.
The successful profiled prototype compiled in 44 seconds, with kernel checking of the
terminal proof taking 1.9 seconds. No timeout or kernel-checking limit was raised.

The core node's old statement edge back to its parent would have created a cycle once
the parent's use of the core was recorded. The accompanying change record explains the
repair of this setting dependency. No mathematical statement was changed.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SectionEvaluation": "b6a7feff0b52bf8c2105b4df431cabd6c00eee41"}, "results": {"Sheaf.Paper.RationalP1FirstTraceTransport": {"hash": "770dd6623b95b679aa7caada85cca47687899add", "status": "OK"}, "Sheaf.Paper.RationalP1FirstTraceTransportCore": {"hash": "25a633feefafb9e4b99d6c68a26dab6e33476922", "status": "OK"}, "Sheaf.Paper.RationalP1FirstTraceTransportCounit": {"hash": "2c28b2e05f5ba97f66679a09af1ea4fc471a63db", "status": "OK"}, "Sheaf.Paper.RationalP1UnitFactorization": {"hash": "21abb0b9c01c4e35b602a4ac2ed1c59b6fb3eb1a", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T06:36:53+0800", "transitive": 0, "version": 1}
```

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
