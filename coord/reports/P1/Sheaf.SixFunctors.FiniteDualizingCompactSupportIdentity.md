## What changed

Proved `WeilConjectures.finiteDualizing_compact_support_identity` in
`Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity`, preserving its exact statement.
The proof specializes the existing general compact-support cocycle to two identity
coefficient changes. Canonical scalar-adjunction unit laws and naturality reduce
this cocycle to the desired equality by cancellation of its invertible component.
Positive-level coefficient finiteness supplies that invertibility through the
existing `compactSupport_isIso` proof.

Added four proved private helpers in the item module: `derived_comp_unit`,
`scalar_comp_unit`, `cocycle_unit`, and `compact_identity`. Added only proof imports:
`import all Sheaf.Paper.FiniteSmoothCompactQuotientCocycle` and
`import all Sheaf.Paper.ExceptionalCoefficientComparison`, for their existing
proved general helpers. Updated the item's DAG proof, proof dependencies, and
proof origin. No other existing module or declaration changes.

Validation: `lcompile.py` compiled the complete item without errors or warnings
in 9.5 seconds. The delivery tool performs the final compile and axiom probes.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.finiteDualizing_compact_support_identity`
(node `lem-coef-dualizing-compact-support-identity`).
No holes added or split off. No `sorry` remains in the delivered module.
All four private helpers have complete proofs. Imported declarations retain their
existing proof status; the delivery does not assert closure of all transitive axioms.
The argument applies to every K, including zero objects, and every positive level
n+1, including n=0. It imposes no extra constructibility, Tor, or flatness hypothesis.

## No longer needed

The former proof dependency `lem-fix-compact-support-coefficient-change`
(`Sheaf.Paper.EtaleCompactSupportCoefficientChange`) is unnecessary for this
identity proof: its bounded-below coefficient-model interface is bypassed by the
already proved ambient proper/open cocycle. It is removed from this node's
proof dependencies, and no proof import of its module is added.
No existing import is removed, and no module is withdrawn or claimed to leave the
targets' import closure: the unchanged public `FiniteDualizingData` interface and
other users can still depend transitively on the coefficient-change module.
The original compact-scalar and scalar-composition dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The previous node plan proposed proving separate identity normalizations of the
proper and open factors. The existing general `compact_chain` helper already
pastes those factors and admits arbitrary coefficient homomorphisms. Its identity
specialization, invertibility, and canonical scalar unit laws give a complete
shorter proof. No statement correction, definition repair, new obligation, or
change to the blueprint unit route is needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity": "20ddc931cf49f3cd3e88d640da031e506a1c901d"}, "results": {"Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization": {"hash": "67ac51c63df58fad88a4d883161231de215ed32a", "status": "OK"}}, "seconds": 22, "time": "2026-10-28T09:23:28+0800", "transitive": 0, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
