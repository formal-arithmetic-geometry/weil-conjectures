# AlgebraicGeometry.ProEtale.relative_profinite_test_labels

## Reason

The statement needs the existing test-object definitions and the component-space
instances. Its proof alone needs the test-functor theorem and pullback pasting.
Remove the unused direct component-profinite theorem import, and keep proof imports
private. The theorem signature and the mathematical meanings of all definitions stay
identical. Two backward elaboration transparency options support the pullback glue;
they change neither declarations nor importer options.

## Old

```lean
public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Topology.SpectralSpace.ConnectedComponent

import all Sheaf.Paper.ProEtalePointComponentsMaps
import all Sheaf.Paper.ProfiniteTestObjectFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
```

The new local file options after `set_option autoImplicit false` are:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

`tools/downstream.py Sheaf.Paper.RelativeProfiniteTestLabels --uses
relative_profinite_test_labels` finds two downstream modules and no textual user of
this theorem outside its defining module. Both direct importers compiled unchanged against the delivered module with
`lcompile.py --all`: `NormalizedContinuousSetComparisonCoherence` in 7.3 seconds and
`NormalizedContinuousSetKanEvaluation` in 8.2 seconds. Neither source uses the removed
component theorem or the proof-only pasting API; their public dependencies already
supply the other required declarations. No definition used by a target changes, so
no target statement review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RelativeProfiniteTestLabels | M2 | Same theorem signature; proof completed. |
| Sheaf.Paper.NormalizedContinuousSetComparisonCoherence | R6 | No adaptation; unchanged source compiled against delivery. |
| Sheaf.Paper.NormalizedContinuousSetKanEvaluation | R7 | No adaptation; unchanged source compiled against delivery. |

## Status

landed 20261023T103104-L-3049897 2026-10-23 (merge of deliver/M2/Sheaf.Paper.RelativeProfiniteTestLabels)
