# ordinaryClopenEvaluation: public API extraction

## Reason

The assigned module contains the ordinary realization/comparison definitions and
its proved module-compositor equation before the remaining theorem. Its lower
normalization and arrow-factor statements need those same definitions without
importing the theorem that combines them. Extraction prevents that import cycle.
No source-library file is changed.

## Old

The original module starts its dependency header with exactly:

```lean
public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
```

It then defines ordinaryRealization_existsUnique through ordinaryOpenComparison
and proves ordinaryModuleEvalG_comp.

## New

The assigned module now publicly reexports the API with:

```lean
public import Sheaf.AlgebraicGeometry.VaryingRingOrdinaryModuleComposition
```

VaryingRingOrdinaryEvaluationComparisons contains that original definition prefix,
with its two public imports unchanged. Every original definition body and theorem
proof in that prefix is preserved. In particular ordinaryRealization still uses
its proved unique specification, its equality still uses choose_spec, and the
comparison isomorphisms retain their original equality transports and associators.

VaryingRingOrdinaryModuleComposition publicly imports this definition module and
retains the original ordinaryModuleEvalG_comp proof and its private helpers. The
assigned module publicly imports VaryingRingOrdinaryModuleComposition. Thus every
original public name, signature and visibility remains available to its importers,
and every original public import remains publicly reachable. Moved docstring blueprint references
attach to the two extraction nodes. The source constructions and their meanings
are unchanged. The separate modules keep their separate compilation costs below
the per-file limit.

The assigned theorem adds private proof imports for its normalization and two
arrow factors and for proved generic comparison-pasting calculation. No existing
module besides the assigned module is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | unclaimed | Compile original unchanged against delivery. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | unclaimed | Compile original unchanged against delivery. |

Both original consumers compile against the delivery without adaptations. Their
actual compile results and timing comparison are recorded in report.md.

## Status

landed 20261027T054600-L-966087 2026-10-27 (merge of deliver/E9/Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation)
