# AlgebraicGeometry.quasiCompact_affine_of_h1_ideal_zero

## Reason

The source assumes that X itself is quasi-compact. QuasiCompact (𝟙 X) only says that the identity morphism preserves quasi-compact preimages, and holds for every scheme. It cannot supply CompactSpace X. For example an infinite disjoint union of field spectra has vanishing H¹ for every quasi-coherent ideal but is not affine. Replace this erroneous encoding by CompactSpace X, exactly as the DAG and Stacks Tag 01XF already say. This is a correction of an intermediate statement, not a target signature or definition change.

## Old

```lean
theorem quasiCompact_affine_of_h1_ideal_zero (X : Scheme.{u})
    [QuasiCompact (𝟙 X)]
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X
```

## New

```lean
theorem quasiCompact_affine_of_h1_ideal_zero (X : Scheme.{u})
    [CompactSpace X]
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules)) :
    IsAffine X
```

## Users

The read-only downstream.py search with --uses quasiCompact_affine_of_h1_ideal_zero reports only the item itself and SerreCriterionAffineness. All other import descendants retain the same statements and definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuasiCompactH1Zero | S2 | Corrected compactness binder; proof rewritten. |
| Sheaf.AlgebraicGeometry.SerreCriterionAffineness | unclaimed in this checkout | Already has [CompactSpace X]; its original source compiles unchanged against the corrected theorem. No adaptation is needed. |

Second-reading import cleanup: the direct public import of
Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact is redundant through the unchanged
public IdealSheaf.Module → IdealSheaf.Subscheme → Morphisms.QuasiSeparated imports.
Its removal therefore preserves the exported dependency set. The redundant proof
import Mathlib.Topology.Separation.Basic is removed as well. The unchanged direct
caller was checked against the cleaned-up delivery.

No definition used by a Challenge target changes and none of the five Challenge signatures changes.

## Status

landed 20261012T202252-L-708722 2026-10-12 (merge of deliver/S2/Sheaf.Paper.QuasiCompactH1Zero)
