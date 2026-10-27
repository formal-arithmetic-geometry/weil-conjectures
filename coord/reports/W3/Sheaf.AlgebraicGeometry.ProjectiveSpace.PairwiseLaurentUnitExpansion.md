## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.exists_pairwise_laurent_unit_expansion`
without changing its signature or either structural constant definition.
Only the assigned Lean module and its own DAG node change.

The proof uses the existing `chartRingEquiv` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial` and
`basicOpen_coordRatio` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundary` as private
proof imports. The two Mathlib proof imports supply `MvPolynomial.X_prime`
and `MvPolynomial.isUnit_iff_eq_C_of_isReduced`.

The proved private helper `exists_unit_zpow_of_localization` clears a denominator
of a unit in a localization away from a prime. Mathlib's
`IsLocalization.Away.algebraMap_isUnit_iff` and `dvd_prime_pow` identify the
numerator as a prime power times a unit of the original ring. Cancellation in
the unit group gives an integral exponent. The second proved private helper
`exists_overlap_unit_expansion` applies this to the j-th polynomial chart,
classifies its units as scalar constants, and compares restrictions from the
two charts. Choice assembles the exponents and coefficients for the family;
the unused diagonal is assigned zero and one.

Validation: the complete module compiled cleanly through `lcompile.py` in
5.4 seconds. The delivered theorem retains the original `3 <= r` hypothesis,
although the calculation works for any two distinct indices. No dimension or
characteristic assumption was added. For equal indices the conclusion is
conditional on a contradiction, exactly as before; no overlap unit is discarded
for distinct indices. The zero scalar is excluded by the unit theorem.
The declaration-scoped unused-variable linter setting accommodates the original
nondependent named index binders in the existential function types.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProjectiveSpace.exists_pairwise_laurent_unit_expansion`
(node `new-sfb-projective-pairwise-laurent-unit-expansion`).

Both new private helpers are fully proved. Holes added: 0. Holes left: 0.
This is a proof, not a decomposition.

## No longer needed

The planned dependency `def-weil-laurent-polynomial-ring` and its Mathlib module
`Mathlib.Algebra.Polynomial.Laurent` are unnecessary for this proof. The argument
uses localization at the prime coordinate instead of constructing Laurent
polynomial coordinates and comparing extremal exponents. Removed that node
from this node's proof dependencies. This does not claim the Laurent polynomial
module is globally unused. No pre-existing import was removed and no module was
withdrawn. The chart and transition definitions and the unit route remain in use.

## Where the brief, the DAG or earlier work was wrong

The old proof plan named only the polynomial, Laurent polynomial, and transition
definitions. It did not identify the already proved polynomial-chart equivalence
or the basic-open localization theorem. Those APIs suffice to close the entire
unit expansion without another split. The node's proof now records the actual
localization argument, whose geometric source is still the double-overlap
calculation of Stacks Tag 0BXJ, divisors lemma-Pic-projective-space-UFD.
No false statement or definition repair was needed. No other existing module,
public interface, target statement, or unit route changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseLaurentUnitExpansion": "66b678c1ffb71467768bfb355c0bf055d8b3e773"}, "results": {"Sheaf.AlgebraicGeometry.ProjectiveSpace.PairwiseCocycleNormalization": {"hash": "222eabfd1bcb697147a4621aa7cc570b7a7576e8", "status": "OK"}, "Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleOffDiagonal": {"hash": "0a3a642571bf32e42e2b4bd9a0023f641e5e0db2", "status": "OK"}}, "seconds": 14, "time": "2026-10-28T04:07:54+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
