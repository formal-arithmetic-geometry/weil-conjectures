## What changed

Proved `AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients`
from the two already stated local-chart lemmas. Obtain `Z`, its inclusion and point,
`a` and `c` from the q lemma; obtain `b'` from the q-prime lemma using those exact
witnesses; pair both equations for every section. No new split and no statement change
to the item. Both existing proof imports are used. A proved private logical helper
performs the dependent existential pairing for arbitrary schemes and quotient maps; this prevents the
kernel from repeatedly expanding concrete relative-Proj and pullback data. Profiling
the direct existential-elimination proof showed 99 seconds in kernel type checking,
while elaboration took less than one second. The final general-helper proof compiled
in 7.0 seconds, with kernel checking at 146 milliseconds. The repaired dependency
compiled in 6.4 seconds. Profiling options were removed before delivery.

Repaired the unclaimed module
`Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime`:
replace the arbitrary `q'` binder by the normalized quotient already specified in
the parent. Update its DAG statement, Lean signature record, proof plan and complete
citer audit. The repair is recorded in
`coord/changes/symmetric-proj-normalized-qprime.md`.

## Proved and sorry left

Closed 1 of 1 holes in the item:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients`.
The item now contains zero `sorry`. Added zero holes; split off zero statements.

The changed dependency retains its one existing hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients_qprime`
(node `lem-trf-symmetric-proj-pullback-generator-local-coefficients-qprime`).
This is an existing statement repair, not a hole closed by weakening its statement.
Its source and complete proof in words are in its docstring and DAG node.

The unchanged dependency
`AlgebraicGeometry.SymmetricProjTautologicalCharts.normalized_pullback_generator_local_coefficients_q`
(node `lem-trf-symmetric-proj-pullback-generator-local-coefficients-q`)
also remains unproved. Thus this delivery proves the parent from its existing
stated dependencies; it does not claim those dependencies are sorry-free.

## No longer needed

None. Both existing proof-dependency nodes and modules are used. No imports or
modules were removed, and no unit route was bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired in this delivery): the previous q-prime declaration
asserted the common-coefficient equation for an arbitrary morphism `M ⟶ D'.line`.
For `E = k²`, on the affine chart of `P¹` with tautological quotient `(1,t)`,
choose `a = 1` and `c = (1,t)`. The arbitrary morphism `(0,1)` cannot equal
`c • b'`: the first basis vector forces `b' = 0`, the second forces `1 = 0`.
Only the normalized second quotient has the required fraction compatibility.
The original natural-language node already described a normalized quotient;
its vague statement is made explicit and its Lean record is corrected.

The sole DAG citer is the item's node; its use holds unchanged because it needs
exactly that normalized quotient. The sole direct Lean importer is the item,
whose signature is unchanged. No other transitive importer mentions the repaired name.

Edge cases: empty `Z` and zero coefficient rings use the unique zero sections;
`E = 0` gives empty symmetric Proj, so the point premise is impossible.
The first frame and coefficient map are kept unchanged when combining the lemmas.
The unit `sk-i-curve-zero` has no realized step replaced by this argument.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficients": "200717e09399785ed18be7530448143c55a90348", "Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorLocalCoefficientsQPrime": "6353abefa44ad5ff81ba0843ee77042dfb05e884"}, "results": {"Sheaf.AlgebraicGeometry.SymmetricProjPullbackGeneratorCrossTensor": {"hash": "4503f928542082bcb66db28100eb2235be755bc3", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T10:23:35+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
