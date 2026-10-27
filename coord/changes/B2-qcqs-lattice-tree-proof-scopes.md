# qcqs_constructible_integral_lattice_tree

## Reason

The proof opens the existing scheme namespace and intermediate-field notation for
recursive pullback refinements and the finite simple extension used for constant
algebraic-closure scalars. These scope commands trigger the conservative interface
checker; every public signature and definition body remains verbatim. The new
helpers are private and fully proved. Unused proof imports are removed.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject
```

```lean
import Sheaf.Paper.ContinuousLocallyFreePullback
import Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import Sheaf.AlgebraicGeometry.InternalExtensionInverseImage
import Sheaf.Paper.CartesianCoefficients
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj ZeroObject IntermediateField
```

```lean
import all Sheaf.SixFunctors.ConstructibleOpenClosedRefinement
import all Sheaf.Paper.FiniteEtaleLocallyFreeModels
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Sheaf.Paper.CartesianCoefficients
```

All public imports stay verbatim. `import all` is private to this module and
makes existing proved private helpers available only to its proof. No source
library module is edited. The six public declarations have unchanged signatures,
and all five existing public definition bodies are unchanged. No target meaning
changes and no statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | B2 | Proof completed; public interface unchanged |

`tools/downstream.py` reports zero downstream modules. Its `--uses` searches for
both `qcqs_constructible_integral_lattice_tree` and `LatticeRefinementTree` find
only the item itself. No consumer adaptation is needed.

## Status

landed 20261023T134847-L-2791837 2026-10-23 (merge of deliver/B2/Sheaf.Paper.QcqsConstructibleIntegralLatticeTree)
