# CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_fpqc

## Reason

Only the proof and its elaboration scope change. The existing theorem signature and all
three public imports are unchanged. The private coproduct proof uses `CategoryTheory.Limits`;
the proof-only algebra descent import is replaced by the affine-case module. This record
accounts for the module-command/import change detected by the delivery checker.

## Old

```lean
import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra
open AlgebraicGeometry CategoryTheory
```

```lean
theorem isEffective_of_isAffineHom_fpqc {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y) {V : Over X}
    [IsAffineHom V.hom] (D : Over.DescentDatum p V) : D.IsEffective
```

## New

```lean
import Sheaf.AlgebraicGeometry.AffineFlatDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
```

```lean
theorem isEffective_of_isAffineHom_fpqc {X Y : Scheme.{u}} (p : X ⟶ Y)
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y) {V : Over X}
    [IsAffineHom V.hom] (D : Over.DescentDatum p V) : D.IsEffective
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineFpqcDescent | H2 | private helper and proof elaboration only; signature unchanged |

No existing declaration or public import changes. Downstream statements and definitions
retain their meaning; no target definition review is reopened.

## Status

landed 20261012T060738-L-2907709 2026-10-12 (merge of deliver/H2/Sheaf.AlgebraicGeometry.AffineFpqcDescent)
