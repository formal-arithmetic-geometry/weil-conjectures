# AlgebraicGeometry.Scheme.Modules.moduleCup_single_pairing_homology

## Reason

The assigned source is absent from the repository. Reconstruct it and prove its
formula from normalized tensor cycles and the global cup diagram. The previous
landing lacked the class-comparison source. Another delivery restored that
source during this reading; the final set uses it unchanged and supplies no
adaptation of it. The normalized tensor interface is also already present.

## Old

The repository has no source module `Sheaf.Paper.ModuleCupSinglePairingHomology`.
The abandoned sandbox tensor interface had conclusion `True` in its cycle field
and could not imply the assigned formula.

## New

The assigned theorem keeps its earlier sandbox parameters and conclusion.
Its proof uses the normalized tensor-cycle formula and two proved helpers.
The class-comparison source now in the repository unfolds the comparison wrapper
to its definitionally identical natural-transformation component; this set uses
that source unchanged. The main signature explicitly imports the naive/derived
module for the wrapper it names. No definition or existing signature is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupSinglePairingHomology | K1 | Reconstructed formula proved |

No existing library module is adapted and no Challenge statement changes.

## Status

landed 20261014T025139-L-157119 2026-10-14 (merge of deliver/K1/Sheaf.Paper.ModuleCupSinglePairingHomology)
