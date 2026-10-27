# Sheaf.Paper.EmbeddedLatticeCoefficientComparison

## Reason

Record the import pruning and local instance commands accompanying the proof repair.
The declaration signatures and all existing definition bodies are unchanged. The
two cached slice sheafification instances avoid repeated instance search in proofs.
They are local attributes and do not register global instances for importers.

The coefficient telescope is proved directly by compact-test bounded denominators,
instead of specializing the finite-subfield coefficient theorem to the arbitrary
carrier `E`. The coefficient-comparison and embedded-image steps of the unit remain.
The two new private proof imports isolate scalar-extension local fractions and
canonical rationalization. Neither adds a name to an existing public signature.

## Old

The old import block, verbatim:

```lean
public import Sheaf.Paper.EmbeddedEllLattice
public import Sheaf.Paper.IntegralScalarConstructibleImage
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.PadicIntegersInvertEll
import Sheaf.CategoryTheory.SheafTensor
public import Sheaf.Paper.LatticePairRestriction
```

There was no local instance-attribute command in the namespace.

## New

```lean
public import Sheaf.Paper.EmbeddedEllLattice
public import Sheaf.Paper.IntegralScalarConstructibleImage
public import Sheaf.Paper.ContinuousIntegralLocalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Paper.LatticePairRestriction
import Sheaf.Paper.LatticeScalarExtensionFractions
import Sheaf.Paper.FullEmbeddedLatticeRationalization
import Sheaf.Paper.ContinuousIntegralRegularTelescope
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.CategoryTheory.Limits.Types.Filtered
```

The following command is local to the namespace/file:

```lean
attribute [local instance] latticeWeakSheafifyOver latticeWEqualsOver
```

The removed direct public import `CochainTensorUniverses` is already supplied by
the retained public statement dependencies. No public declaration, definition,
instance, or notation is removed. The removed private imports are not used by
this proof. Existing upstream declarations and their dependencies are preserved.

## Users

`python3 tools/downstream.py Sheaf.Paper.EmbeddedLatticeCoefficientComparison
--uses embedded_lattice_coefficient_comparison` reports zero downstream modules
and the declaration's own module as its only textual user (2026-10-23).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EmbeddedLatticeCoefficientComparison | V9, dispatched item | Proof compiles with the pruned imports and local instance cache; signatures and definitions unchanged. |

No consumer adaptations are required. DAG parents with unfinished proofs retain
the original theorem and its complete signature. No target meaning changes.

## Status

landed 20261024T021124-L-2713417 2026-10-24 (merge of deliver/V9/Sheaf.Paper.EmbeddedLatticeCoefficientComparison)
