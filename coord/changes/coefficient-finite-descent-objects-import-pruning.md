# coefficient_finite_descent_objects

## Reason

The proof uses the existing upstream object-descent theorem and a proved comparison of
constructibility predicates. Its direct cone, lisse and triangulated proof-plan imports
are unused. The public re-export of Derived.BoundedConstructible is also unused by the
statement and proof. Remove these imports and add the actual proof dependencies. No
existing declaration signature, visibility, definition or target changes. The consumer
checks below confirm that the removed public re-export was unnecessary for both direct
consumers. The target statements and the definitions they use retain their meanings.

## Old

```lean
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.Paper.CoefficientFiniteDescentHom
import Sheaf.Paper.CoefficientFiniteDescentLisse
import Sheaf.Paper.CoefficientHeartGeneration
import Sheaf.Paper.CoefficientHeartTriangulated
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
```

## New

```lean
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ConstantModelBoundedConstructibleComparison
```

The signature of `AlgebraicGeometry.ProEtale.coefficient_finite_descent_objects` is identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | not adapted; no current claim found | Compiles unchanged against delivered artifacts in 51.5 s. Its theorem statement and own public imports are unchanged. |
| Sheaf.SixFunctors.IntegralModelsGenerators | not adapted; no current claim found | Compiles unchanged against delivered artifacts in 20.7 s. Its theorem statement and own public imports are unchanged. |

These are both direct consumers. No adaptations are delivered. Transitive consumers retain
exactly the same exported declarations from these unchanged consumer modules.

## Status

landed 20261019T112546-L-3955404 2026-10-19 (merge of deliver/U5/Sheaf.Paper.CoefficientFiniteDescentObjects)
