# Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization public imports

## Reason

The completed proof does not use the intrinsic closed ambient adjoint,
intrinsic extension-by-zero adjunction, or general locally closed coherence
modules. Its existing public definitions only need the intrinsic transport API
from `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`. Import that API
directly and prune the three broader public imports. All existing declaration
signatures, attributes, visibility and non-theorem bodies remain unchanged.
The private proof imports provide the fixed-coefficient adjunction and the
proper/open comparison actually used in the proof.

This changes transitive import exposure, so independent review is required.
It does not change a mathematical definition or any target statement's meaning.
No source-library file or other group's module is changed.

## Old

The original public-import block, verbatim:

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Adjunction.Mates
```

## New

The replacement public-import block, verbatim:

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SixFunctors.EtaleLocallyClosedExtensionComparison
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Adjunction.Mates
```

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization`
reports zero downstream Lean modules. The import-pruning check also passed.
The DAG still needs this item: its unfinished parent is retained, and the item's
complete public declaration interface remains available to that parent's proof.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization | S8 | Compiles unchanged statements and definitions against the precise public imports. |
| Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison | unclaimed | Anticipated DAG consumer; no current Lean import, no signature change or adaptation. |

## Status

landed 20261021T130149-L-2576697 2026-10-21 (merge of deliver/S8/Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization)
