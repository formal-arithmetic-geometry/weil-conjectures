# AlgebraicGeometry.ProEtale.integralConstructibleCompactness

## Reason

The original theorem is reduced to three strict intermediate arguments: integral Ind
realization and image closure, integral lower-tail vanishing, and continuity on one finite
cohomological window. The assembly is proved in Lean. Private categorical helpers handle
Hom exactness, support sizes for existing large coproducts, naturality of the direct-sum
comparison, and bounded devissage followed by reflection of compactness.

A generic private assembly lemma avoids repeated normalization of the concrete monoidal
module category. The retained concrete assembly exhausted the ordinary heartbeat budget;
the generic assembly compiles. The window proof similarly isolates the categorical assembly
from the concrete integral module category and caches the coproduct instances used repeatedly
by the truncation comparisons. The lower-tail proof also abstracts its filtered-colimit factorization and endpoint
truncation argument into private categorical helpers; its unchanged public theorem
then compiles in 10.5 seconds. No computational limit was raised. The static interface checker reports only additional
commands used to scope the private proofs. Public signatures, declaration visibility,
definition bodies, and public imports are identical. No target definition changes.

## Old

```lean
universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
```

The public theorem body was `by sorry`. The definition
`IntegralConstructibleCompactnessAssertions` is unchanged verbatim.

## New

```lean
universe w v u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
```

There are local `open Classical in` commands on private proof helpers. All added helpers
are private and proved. The public theorem has its original signature and now applies the
proved private assembly to the three new intermediate statements and the existing
localizing-closure theorem. Every new dependency is a private proof import. No existing
public import was changed. This record documents the checker-visible proof commands;
there is no altered mathematical interface and no target review to reopen.

## Users

No consumer mentions a changed public declaration, since none changes. The search
`tools/downstream.py ... --uses integralConstructibleCompactness` returned no uses.
The three direct importers are listed below; no module is adapted. Their imports see the
same declarations with the same types, definitions, and public imports. Holder status
is irrelevant to this set because no consumer file is included or edited.
All three original consumer files were copied unchanged into a separate consumer-check
sandbox and compiled successfully against the modified item and its three new imports.
The final validation results are recorded in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralProperDirectSums | not adapted | Same public interface; no changes. |
| Sheaf.Paper.BrownHypothesesGeneration | not adapted | Same public interface; no changes. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | not adapted | Same public interface; no changes. |

## Status

landed 20261019T154008-L-3025015 2026-10-19 (merge of deliver/E7/Sheaf.Paper.IntegralConstructibleCompactness)
