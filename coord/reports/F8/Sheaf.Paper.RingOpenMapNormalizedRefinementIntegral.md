## What changed

Proved `exists_normalized_refinement_iso_integral` in
`Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral` by reusing the existing
`WeilConjectures.sfQcqsCompletedRefinement_exists`, imported privately from
`Sheaf.Paper.QcqsCompletedRefinement`.

The input's finite-Tor predicate contains its integral constructibility predicate.
Repackage the same ambient derived object with that property. The proved
`PurCompactSupport.coefficientPrimeUnit` supplies invertibility of l in D.k.
The existing qcqs theorem supplies a compact-support isomorphism together with
`SfCompletedRefinementSpec`; extract its open/proper isomorphism and transpose
normalization. Its completed coefficients and the integral RingStage coefficients
are definitionally identical. The two proofs of coefficient pullback composition
agree by proof irrelevance. No target, declaration signature, definition, or public
import changed. The item's DAG proof and proof dependencies now record this route.

Validation: `lcompile.py` compiled the changed module cleanly in 7.4 seconds.
The import-direction check confirmed that QcqsCompletedRefinement does not reach
this item. Delivery performs the required independent server checks.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_normalized_refinement_iso_integral`
(node `lem-sf-ring-open-map-normalized-refinement-integral`).

Zero holes remain in the item; zero holes were added; zero statements were split off.
This proof uses the already-stated theorem
`WeilConjectures.sfQcqsCompletedRefinement_exists`
(node `lem-zl-qcqs-completed-refinement`), whose proof still contains its existing
sorry. It does not claim that transitive dependency has been proved here.

## No longer needed

No imports removed, no modules withdrawn, and no DAG nodes pruned. The existing
assembly-data and refinement-restriction imports remain statement dependencies.
A second construction of the finite-level comparisons and their normalized total
limit inside this item is unnecessary: the existing qcqs completed-refinement
statement already includes the required normalized open/proper isomorphism.
The two original definition/statement dependencies remain in `stmt_deps`; the
updated `proof_deps` names the declarations actually used by the proof.

## Where the brief, the DAG or earlier work was wrong

The item's original proof plan described a fresh strict-reduction construction,
but an existing library statement already supplies the result without absolute
separatedness of X or Y. In contrast,
`PurCompactSupport.refinementProperOpen_existsUnique` in
`IntegralCompactSupportCoefficientComparison` assumes separated structure maps,
so it is not directly applicable. The qcqs theorem has precisely the needed
relative separatedness and finite-type hypotheses and even applies to all integral
constructible objects, including this finite-Tor input. It retains the actual
normalization equation, not merely existence of an unrelated isomorphism.

The same extraction works for zero inputs, empty X, and identity refinements;
it does not add a nonemptiness hypothesis or choose arbitrary data for a definition.
No unit-level proof route is changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral": "594abb17ca081c5b19e7b2e4709023405b7abfb2"}, "results": {}, "time": "2026-10-28T05:08:59+0800", "transitive": 0, "version": 1}
```

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
