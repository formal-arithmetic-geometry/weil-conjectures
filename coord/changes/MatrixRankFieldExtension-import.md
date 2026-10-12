# Sheaf.LinearAlgebra.MatrixRankFieldExtension imports

## Reason
`Mathlib.LinearAlgebra.LinearIndependent.BaseChange` is used only by the proof of
`Matrix.rank_map_field_extension`, so its import must be private under the stage-3 import rule.

## Old
```lean
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
```

## New
```lean
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.ConstantRankMapNormalFormNonempty | other | imports the target module; no declaration from BaseChange is used through it |
| Sheaf.AlgebraicGeometry.Modules.ConstantRankMapNormalForm | other | imports the target module; no declaration from BaseChange is used through it |

## Status
landed 20261012T184241-L-3995518 2026-10-12 (merge of deliver/B2/Sheaf.LinearAlgebra.MatrixRankFieldExtension)
