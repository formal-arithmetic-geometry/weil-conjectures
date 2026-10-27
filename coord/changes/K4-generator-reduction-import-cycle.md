# GeneratorReductionStatement proof-dependency interface

## Reason

The parent must import the existing tensor/adjunction and open-square theorems to
implement its stated proof. Both lower modules still publicly import the parent,
although they use only the definitions already extracted verbatim to
Sheaf.SixFunctors.GeneratorReductionData by T7. The new parent imports therefore
force an import cycle. Change exactly that one import in each lower module to the
existing data owner. This is an import-only forced adaptation; all existing
signatures, declaration visibility, attributes and theorem bodies remain identical.

The originals were checked with lcompile.py --all in the packet's
scratchpad/original-cycle copy, against the new parent and substitution module.
Its import-order diagnostic is:

```
the modules import one another in a cycle:
Sheaf.SixFunctors.GeneratorReductionStatement,
Sheaf.SixFunctors.OpenInterchangeReductionSquares,
Sheaf.SixFunctors.StructuralReductionWordSubstitution,
Sheaf.SixFunctors.TensorAdjunctionReductionSquares
```

The wrapper reports exit 2 because its detached process exits during import ordering;
the underlying diagnostic is the import cycle, not a Lean time limit or server failure.
The adapted four-module packet is checked separately using normal lcompile.py --all.

No target declaration or definition changes. The parent's public imports stay identical.

## Old

In both Sheaf.SixFunctors.TensorAdjunctionReductionSquares (line 8) and
Sheaf.SixFunctors.OpenInterchangeReductionSquares (line 23):

```lean
public import Sheaf.SixFunctors.GeneratorReductionStatement
```

## New

In both modules, at those same lines:

```lean
public import Sheaf.SixFunctors.GeneratorReductionData
```

The lower modules re-export all the data they actually use and no longer re-export
the parent theorems. The source-tree downstream scan found zero existing importers
of either lower module, so no existing consumer loses a required declaration.

## Users

Read-only tools/downstream.py scans of both adapted modules returned zero existing
downstream modules. The new delivery's users are included below. Holders were read
from coord/claims on 2026-10-25.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | C2 | Forced import at line 8 only; declarations identical. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | E3 | Forced import at line 23 only; declarations identical. |
| Sheaf.SixFunctors.GeneratorReductionStatement | K4 | Imports the two lower proofs without a cycle; existing signatures identical. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | new in this delivery | Uses Structural and StructuralSquares from the open-square module. |

## Status

landed 20261025T180837-L-4040248 2026-10-25 (merge of deliver/K4/Sheaf.SixFunctors.GeneratorReductionStatement)
