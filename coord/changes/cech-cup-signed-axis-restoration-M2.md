# cupCech_signed_axis_pairing

## Reason

The returned landing was withdrawn, so the assigned module and node are absent
from the current baseline. Recover the returned proof from the recorded repair
diff and restore the exact original statement. The original `import all
Sheaf.Paper.CechCupProduct` exposed private declarations of its dependencies,
causing the reported duplicate symmetric-category instance when imported.

## Old

The module is absent in the current baseline. The returned version had:

```lean
public import Sheaf.Paper.CechCupProduct
import all Sheaf.Paper.CechCupProduct
```

## New

```lean
public import Sheaf.Paper.CechCupProduct
import Mathlib.LinearAlgebra.Quotient.Bilinear
```

The proved private cycleClassLinear, cycleClassLinear_eq_zero,
bilinear_homology_desc, cycle_d_zero, cycle_mem_range_of_d and toCycles_zero helpers are reproduced
locally from CechCupProduct. The public theorem signature and all six axis
hypotheses are unchanged. No other module or signature is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CechCupSignedAxisPairing | S3 | Restore original statement with repaired imports. |

No current source module imports the withdrawn module. The returned self-importer
failure is addressed by making this module importable without exposing the
private dependency environment; no consumer adaptation is needed.

## Status

landed 20261014T073818-L-3476848 2026-10-14 (merge of deliver/S3/Sheaf.Paper.CechCupSignedAxisPairing)
