# AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen

## Reason

The statement only needs schemes, fields and algebras, finite-type and quasi-compact
morphisms, pullbacks, open immersions and topological Krull dimension. The original module
re-exported unused tensor, inverse-image module, sheaf, ring-colimit and Picard APIs.
The proof now reuses two complete source-library results through ordinary proof imports.
Prune unused imports, including their unnecessary public exports.

## Old

```lean
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Topology.InverseImageModule
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
```

The theorem signature is unchanged.

## New

```lean
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
```

The theorem signature is unchanged. No definition is changed.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DimensionExtension --uses
AlgebraicGeometry.topologicalKrullDim_fieldExtension_and_denseOpen` lists these three
importers and no external textual use of the theorem. Each retains its original source;
all three have their own statement imports and use this module only as a proof dependency.
The import-pruning check reports no lost declaration use.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DimensionExtension | Y3 | Same theorem, proof closed; unused public imports removed. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | unchanged, not adapted | Own public coefficient/module/tensor imports; no signature change. |
| Sheaf.AlgebraicGeometry.OpenProductExchange | unchanged, not adapted | Own public exchange imports; no signature change. |
| Sheaf.TraceFormula.FlatFpRelativeDimensionDenseOpen | unchanged, not adapted | Own public finite-presentation/open-immersion/fibre imports; no signature change. |

No target statement or definition used in a target is changed. No forced adaptations.
All three unchanged direct importers were compiled against the delivered DimensionExtension
in a scratch sandbox using lcompile.py --all; all passed (1.6 s, 1.7 s, 0.1 s respectively).
The independent reader should also check this public-import removal.

## Status

landed 20261018T150152-L-3801249 2026-10-18 (merge of deliver/Y3/Sheaf.AlgebraicGeometry.DimensionExtension)
