# EtaleComplexPageDiagram public imports

## Reason

The proof uses restriction homology and the termwise hypercohomology API. The
other direct public imports are redundant and make the file exceed the isolated
compile limit; all declarations remain available through the retained public
import or through proof-only imports. No declaration signature changes.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Sheaf.Paper.EtaleTermwiseHypercohomology
```

## New

```lean
public import Sheaf.Paper.EtaleTermwiseHypercohomology
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Sheaf.AlgebraicGeometry.EtalePageMapCoherence
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| TargetsCheck | none recorded | declarations and signatures unchanged; retained imports provide all public names used downstream |

## Status

landed 20261012T220523-L-1394619 2026-10-12 (merge of deliver/P1/Sheaf.AlgebraicGeometry.EtaleComplexPageDiagram)
