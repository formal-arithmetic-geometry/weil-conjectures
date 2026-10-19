## What changed

Proved all three original holes in `Sheaf.Paper.IntegralDerivedReduction`, with every
existing declaration signature and definition unchanged.

`integralDerivedReductionProjection_locallySurjective` refines the covering image sieve
of the finite constant-sheaf unit. A quotient representative lifts to the valuation ring;
its constant section maps to the completed sheaf by the existing limit-cone construction.
The limit projection equation and sheafification naturality identify its reduction with
the given local representative. This handles exponent one, arbitrary site objects,
independent coefficient/site universes, and empty covering sieves without extra hypotheses.
The local-surjectivity instance for commutative-ring sheafification is transported through
the existing small-model theorem.

`integralDerivedReduction_exact` and `integralDerivedReduction_counit_isIso` use the
exactness and K-flat computation conjuncts of the defining universal derived-pair witness.
Added the proof-only import `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.

Removed four redundant public imports, retaining their entire public import closure through
the remaining public imports. The public K-flat resolution import is retained to preserve
the existing exported interface for consumers. See
`coord/changes/B4-integral-derived-reduction-imports.md`.

Validation: the item compiles cleanly with no holes. The projection theorem's printed
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`. The exactness and
K-flat-counit theorems additionally use `sorryAx` through the pre-existing general theorem
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients`; they introduce no new hole.

## Proved and sorry left

Closed 3 original holes:

- `WeilConjectures.integralDerivedReductionProjection_locallySurjective`.
- `WeilConjectures.integralDerivedReduction_exact`.
- `WeilConjectures.integralDerivedReduction_counit_isIso`.

Zero holes remain in the item. Zero holes added; zero statements split off. These are
proofs from the existing dependencies, not a decomposition into new assumptions.

## No longer needed

Removed redundant direct imports:

- `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`.
- `Sheaf.Algebra.Homology.KFlat`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.

All four remain publicly available through the retained imports. No entire dependency
module or DAG node is claimed pruned: the general derived-change-of-rings construction
still needs its underlying resolution and tensor theory. The original docstring proof
route is followed; there is no unit bypass and no new proof dependency outside the
existing completed-coefficient and derived-change-of-rings nodes.

## Where the brief, the DAG or earlier work was wrong

The node `def-weil-integral-derived-reduction` currently attaches its primary Lean record
to the unrestricted sibling `scalarReductionDerivedExtension` in
`Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, rather than to the dispatched
finite-field presentation. Its attachment and statement are left unchanged. The dispatch
is nevertheless substantive: all three original holes of the requested module are closed.
The node has no numbered proof steps; the existing declaration docstrings supply the
argument followed here. No statements or constructions were repaired.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
