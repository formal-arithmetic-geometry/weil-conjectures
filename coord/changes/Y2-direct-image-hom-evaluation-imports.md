# AlgebraicGeometry.Etale.DirectImageHomEvaluation.square

## Reason

The proof uses the already published ordinary etale adjunction and comparison interfaces.
Remove unrelated generic ringed-site imports and add the proved canonical signed-symmetry
involutivity theorem as a private proof import. All eight public declaration signatures and
all seven definition bodies remain unchanged. Two backward elaboration transparency
options are enabled to match the published etale definitions during proof rewriting;
they do not change any declaration or install any instance or attribute.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Paper.CoefficientRingedTensorHomModel
```

## New

```lean
import Sheaf.SixFunctors.DerivedTensorSymmetryInvolutive
```

The existing public imports EtaleHomComparisonModels, PurEtaleScalarMateProjection and
EtaleDerivedTensorSymmetry supply every notion in the unchanged statements and definitions.
The proof replaces the single sorry of square with counit and tensor naturality.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DirectImageHomEvaluationSquare | Y2 | proof completed; unused imports removed |

The downstream.py source scan reports zero downstream modules. No consumer adaptations are
required. The statement and definitions retain their meaning, so no target review is reopened.

## Status

landed 20261021T130236-L-2650499 2026-10-21 (merge of deliver/Y2/Sheaf.Paper.DirectImageHomEvaluationSquare)
