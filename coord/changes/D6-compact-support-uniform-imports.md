# compactSupport_uniform_tor_bound public imports

## Reason

Remove unused proof-plan exports while proving the unchanged theorem. Only statement
imports remain public; new proof dependencies are ordinary imports. No definition or
statement changes. The one downstream importer is checked against the pruned interface.

## Old

```lean
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ConstantModelTorAmplitude
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
```

## New

```lean
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
public import Sheaf.Paper.ProjectionCompactification
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
```

The declaration `AlgebraicGeometry.ProEtale.compactSupport_uniform_tor_bound` has exactly
the same signature in both versions.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportUniformTorBound | D6 | same theorem signature; proof completed |
| Sheaf.Paper.SmoothPurityTowerBound | J3 | unchanged; compiled as consumer |

`tools/downstream.py Sheaf.Paper.CompactSupportUniformTorBound --uses
compactSupport_uniform_tor_bound` reports one downstream module, `Sheaf.Paper.SmoothPurityTowerBound`, and only this
module's own declaration as a textual use. The unchanged consumer compiled against the sandbox theorem in the same ordered
server compile: theorem 54.6 s, consumer 29.2 s, exit code 0 (2026-10-19).

## Status

landed 20261019T133210-L-1272491 2026-10-19 (merge of deliver/D6/Sheaf.Paper.CompactSupportUniformTorBound)
