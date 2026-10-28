## What changed

Proved `WeilConjectures.integralDualizing_mapping_limit_hom_at_degree_zero` with its
existing signature. Private helpers carry out the global degree-zero Hom comparison
and the coefficient-point comparison; all mathematical dependencies are existing
statements. The proof applies zeroth homology to the supplied isomorphism and composes
these equivalences. Proof-only imports expose the existing normalized RHom, exact
sections, compact-support representative, point equivalence, and unit calculations.
The node now records those dependencies and the actual proof.

## Proved and sorry left

Closed the single original hole in
`WeilConjectures.integralDualizing_mapping_limit_hom_at_degree_zero`.
Holes closed: 1. Holes added: 0. Split off: 0.
No `sorry` remains in the delivered module. All private helpers are proved.
The proof uses existing project declarations, including those still awaiting proofs;
this delivery does not claim to discharge their obligations.

## No longer needed

None. The original public import of `IntegralDualizingRoosModel` is retained.
No previously declared dependency or unit step is bypassed, and no module is withdrawn.
The two private-route results are public split-off statements in new modules; their nodes are listed below.

## New nodes

`lem-coef-integral-dualizing-global-homology-at-zero` and `lem-coef-integral-dualizing-coefficient-homology-at-zero` are the strict degree-zero comparison steps used by the target proof.

## Where the brief, the DAG or earlier work was wrong

The node's original proof described the right argument but listed no proof dependencies.
The proof now records the normalized global RHom comparison, constructibility of the
chosen compact-support limit, full faithfulness of integral point sections, and the
completed coefficient-unit normalization explicitly. No mathematical statement or
shared definition was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingCoefficientHomologyAtZero": "a562edc86f61ac7ff0bcb68aa70d42fabac951f3", "Sheaf.SixFunctors.IntegralDualizingGlobalHomologyAtZero": "61596df405061f0608226993d03e6f0242561dc1", "Sheaf.SixFunctors.IntegralDualizingMappingLimitHomAtDegreeZero": "91089997c6e07be64a55ac5302f946c0214b9c02"}, "results": {}, "time": "2026-10-28T11:06:08+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
