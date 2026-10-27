## What changed

Proved `CategoryTheory.Functor.exactDerivedHomComparison_shift` in
`Sheaf.CategoryTheory.ExactDerivedHomComparisonShift`, with its public signature unchanged.
Added one private proof import:
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal`.
The two existing public imports remain necessary for the statement and definitions.
No other existing Lean module or public interface changed.

The proof uses the canonical derived tensor comparison. Its existing shift theorem handles
one tensor variable; private proved helpers obtain the other variable from
`DerivedCategory.commShift_of_tensorRight_fac` on functorial K-flat resolutions and transport
along resolution isomorphisms. After identifying this comparison with the transported monoidal
structure in the statement, the two tensor shift equations give the tensor interchange square.
Taking adjunction mates gives the raw contravariant internal-Hom square. Equality transport
handles the double negative in `siteHomOppositeSourceShift`. The supplied normalizations multiply
both sides by the same quadratic sign and give `NatTrans.CommShift`.

Updated the item's DAG node's proof, proof dependencies and proof origin to describe this route.
The unit route and statement are unchanged. All helpers are private and completely proved.
The assigned module compiled without warnings in 17.4 seconds through `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Functor.exactDerivedHomComparison_shift`
(node `lem-sf-exact-derived-hom-comparison-shift`).

There are zero remaining `sorry` declarations in the item, zero holes added elsewhere,
and zero split-off obligations. This is a proof, not a decomposition.

## No longer needed

The proof does not use these planned proof dependencies, now removed from this node's
`proof_deps` and proof-step uses:

- `lem-sf-ringed-hom-complex-pullback-shift`, module
  `Sheaf.Algebra.Homology.RingedHomComplexPullbackShift`: ordinary ringed Hom complexes and
  their component signs are unnecessary because the defined source shifts are adjunction mates.
- `lem-pc-kflat-resolution`, module
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: independent-coefficient
  ringed-site resolutions are unnecessary. The existing functorial flat resolution API for the
  arbitrary abelian categories in the statement supplies the required tensor comparison proof.

Neither planned module was imported by the original item, so no existing import line was
removed. Both existing public imports are used; the sole added proof import is used.
These dependencies are pruned from this item's route only; no declaration or module is withdrawn.
No K-injective model, preservation of K-injectives, or invertibility/exactness theorem for the
internal-Hom comparison is required.

## Where the brief, the DAG or earlier work was wrong

The earlier chain-level plan called on ringed-site declarations, whereas this theorem is stated
for arbitrary closed braided monoidal Grothendieck abelian categories. The shorter categorical
route uses existing generic derived tensor shift results and avoids that mismatch. The old
source docstring records the chain-level plan; the updated DAG and inline proof comments record
the implemented argument. No hypothesis, conclusion, definition, universe or target was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.ExactDerivedHomComparisonShift": "2f38a324430583fa70d2f8682d383019f9840c93"}, "results": {"Sheaf.AlgebraicGeometry.SiteHomComparisonThick": {"hash": "29d7a19d3a524d0b2a51e0b5702a9ddfe30b5f2d", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T06:52:10+0800", "transitive": 0, "version": 1}
```

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
