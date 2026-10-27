## What changed

Restored the assigned module and repaired its proof by decomposing the two
independent conjuncts into `scalar_q_chern_splitting` and
`scalar_p2_chern_splitting`. The parent now imports those modules and combines
their results with an explicit pair constructor. The two split modules and DAG
nodes are included in this delivery. All three modules compile in import order.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.RationalP1.scalar_chern_splittings` with a
real proof. Two strictly smaller theorem obligations remain as named split-offs:

- `AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_splitting`, node
  `lem-sfb-rational-p1-scalar-q-splitting` (one `sorry`);
- `AlgebraicGeometry.ProEtale.RationalP1.scalar_p2_chern_splitting`, node
  `lem-sfb-rational-p1-scalar-p2-splitting` (one `sorry`).

No `sorry` occurs in a definition or in the parent proof.

## No longer needed

The parent no longer directly requires its former model/completion proof
dependencies; its proof uses only the two split theorem modules. No existing
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The parent statement packages two independent geometric isomorphism claims,
while the available declarations do not provide either claim directly. The
repair makes each conjunct an explicit, strictly smaller theorem and proves the
parent by pairing them. The reported bad-import build failure is resolved by
restoring the missing proof imports.

## New nodes

`lem-sfb-rational-p1-scalar-q-splitting` records the Q unit/Chern biproduct
isomorphism and its module declaration.

`lem-sfb-rational-p1-scalar-p2-splitting` records the second-projection
unit/Chern biproduct isomorphism and its module declaration.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernP2Splitting": "df4bb074da71f89ddb1593f2638449b7c726d522", "Sheaf.Paper.RationalP1ScalarChernQSplitting": "fab8b5f23cca6022473267d72495b0afa1da19e4", "Sheaf.Paper.RationalP1ScalarChernSplittings": "cb8089e862807e3e960ab382934c4b655948d9e8"}, "results": {"Sheaf.Paper.RationalP1SecondScalarTrace": {"hash": "70acd7b00b358a93fcf8c88dc8ac321dc76dfd70", "status": "OK"}}, "seconds": 47, "time": "2026-10-28T03:02:07+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
