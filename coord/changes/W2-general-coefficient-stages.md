# General coefficient scalar-stage declarations

## Reason

The combined item exceeded the 60-second compilation limit after profiling and
local opacity improvements. Separate the finite scalar-stage argument from the
common-stage pair/colimit construction, as permitted by the worker brief step 3a.
No existing declaration signature or definition body changes.

## Old

The scalar-stage declarations from `Stage` through `stageTransition_additive`,
including the two specialization lemmas moved earlier for the new proofs, were
defined in `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`. Its imports were:

```lean
public import Sheaf.Paper.SfAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Pi.Basic

import Sheaf.Paper.SfIntegralConstructibleTriangulated
```

## New

The same declarations, names, signatures and definition bodies are defined in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`. Their existing private
proof helpers move with them. The item imports:

```lean
public import Sheaf.Paper.SfAlgebraicallyClosedCoefficients
public import Mathlib.CategoryTheory.Pi.Basic
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages
```

The supporting module public-imports `SfAlgebraicallyClosedCoefficients` and retains
the proof-only `SfIntegralConstructibleTriangulated` import. It is imported publicly
because its actual stage definitions occur in the item's public signatures.
The only remaining hole there is the original `associator_cocycle`; it is not a new
split-off theorem. The two newly completed proofs are `transitionCommShift_existsUnique`
and `transitionExact`. All other original holes remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | W2 | Public-import the relocated declarations; retain all public names and signatures. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages | new | Holds the unchanged scalar-stage interface and its proofs. |

Importers of the item continue to receive all original declarations. No existing
shared module besides the assigned item is changed, and no downstream proof needs
adaptation. The item is compiled against its new supporting module in the same packet.

## Status

landed 20261026T235952-L-1474688 2026-10-26 (merge of deliver/W2/Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients)
