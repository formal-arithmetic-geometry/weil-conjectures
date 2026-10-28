## What changed

Filled `WeilConjectures.finiteHomSiteEquationDescent` without changing its signature or
public imports. Added private proof imports of `ScalarHomComparisonTower`,
`NormalizedDVRCompletedRestrictionCoherence`, and `FiniteHomIntrinsicTensorComposition`.
Updated the item's node to the direct evaluation proof.

Validation: `lcompile.py` compiled the final item without errors or warnings in
14.8 seconds. All Lean lines are at most 100 characters; the public theorem
signature is byte-for-byte unchanged.

Naturality and preservation of arbitrary transposes are ambient closed-adjunction
identities. The intrinsic strong monoidal witness in `hmonoidal` supplies internal
composition. The private composition calculation reproduces the existing
`finiteChange_composition` calculation in the parent `FiniteCoefficientHomChange`;
importing that parent would create a cycle.

The quotient tower equation follows by applying the existing scalar Hom tower
calculus to `finiteHomIntrinsic_tensorComposition`. Its self-quotient case also
proves the identity tensor normalization: identify the canonical associator with
`F.map` of the canonical unit using restriction coherence and adjunction mates;
then cancel the tensorator and the faithful functor `F ≅ Id`. The existing generic
scalar Hom identity calculation gives the required unit equation.

## Proved and sorry left

Closed one of one holes: `WeilConjectures.finiteHomSiteEquationDescent`
(node `lem-coef-finite-hom-site-equation-descent`). Zero holes remain in the item;
zero new holes or split-off statements are added. The existing dependency
`WeilConjectures.finiteHomIntrinsic_tensorComposition` remains an existing
unproved tensor square, not a new obligation introduced by this delivery.

## No longer needed

No existing import was removed. The item's old planned proof dependencies
`lem-coef-monoidal-square-hom-transport` / `Sheaf.SixFunctors.CoefMonoidalSquareHomTransport`
and `def-weil-pbc-normalized-origin-scalar-comparisons` /
`Sheaf.Paper.NormalizedOriginScalarComparisons` are not used by this proof.
The latter remains transitively available through the unchanged statement-data
import. This is pruning of this node's proof route, not withdrawal of either module.

The etale-origin equations, constructible descent witnesses, square invertibility,
and quotient site coherence are unnecessary for the ambient equations proved here;
the original theorem keeps all its parameters and both implications verbatim.
No unit statement or unit proof step is bypassed (the recorded unit has no realized
steps). No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan used site descent for laws that follow directly from the actual
evaluation transposes and tensor coherence on the intrinsic category. Its planned
monoidal-square theorem uses a different left-closed convention; a bridge between
closed structures is unnecessary for this direct proof. The existing intrinsic
tensor composition square also controls the identity quotient, so no new
normalization assumption or new lemma with a hole is needed.

Searches used LeanFinder, Loogle, launcher grep and source ripgrep. Mathlib's
exponential comparison results are cartesian specializations; the existing generic
right-closed scalar Hom calculations are the applicable library results.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteHomSiteEquationDescent": "91bf5cda9b568581cfcd3a72a4a788d663171cb0"}, "results": {"Sheaf.Paper.CoefFiniteHomSiteDescent": {"hash": "9ff436f0b1d6dc4ddb9c634bdd3c73cfc7c9f0b6", "status": "OK"}}, "seconds": 161, "time": "2026-10-28T10:18:29+0800", "transitive": 0, "version": 1}
```

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
