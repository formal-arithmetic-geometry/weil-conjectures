## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_unit_factorization` in
`Sheaf.Paper.RationalP1UnitFactorization`, following both steps of its existing DAG plan.
A proved private helper performs the calculation for an unbundled commutative coefficient
object: open the normalization witnesses, convert their HEq to equality, and expand
`unitComponent`, `diagonalClassMap`, and `firstKernelInsertion`. `Functor.map_comp` and
`Category.assoc` give the displayed factorization.

The public theorem specializes this helper. A private congruence builder, adapted from
`FiniteCoefficientProperFormulaTools`, produces ordinary kernel-checked equality proofs
between the native and generic interfaces. This avoids expensive definitional conversion
between sheaf tensor instances. The added proof imports are `Mathlib.Logic.Function.Basic`
and `Mathlib.Lean.Meta.CongrTheorems`. The local irreducibility setting on the derived
pullback/pushforward wrappers was removed to allow the helper's native inverse expression.
The existing public statement, definitions, public imports, and DAG route are unchanged.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_unit_factorization`
(node `lem-sfb-rational-p1-unit-factorization`).

Holes added: 0. Holes remaining in the delivered module: 0. No split-off statements.
All private helpers are proved; the metaprogram only constructs proof terms checked by Lean.
The final module compiled in 26.4 seconds. `#print axioms` for the public theorem reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. Both existing proof dependencies remain necessary: the ambient-composites definitions
and the constructed `firstKernelInsertion` from `RationalP1SectionEvaluation`. Its section
evaluation theorem is not used. No existing import, node, or module was removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The native coefficient specialization triggers an
expensive conversion between definitionally equal sheaf tensor instances; explicit
congruence proofs resolve it without changing a shared definition or the statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1UnitFactorization": "21abb0b9c01c4e35b602a4ac2ed1c59b6fb3eb1a"}, "results": {"Sheaf.Paper.RationalP1FirstAmbientContraction": {"hash": "816047452ecc54db4e313b40dee1180b0a19d2f4", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T03:45:20+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
