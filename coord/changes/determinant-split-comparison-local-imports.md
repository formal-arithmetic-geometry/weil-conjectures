# determinant_split_comparison_restriction imports

## Reason

The corrected naturality theorem uses exterior sheaves, the tensor monoidal instance on
`X.Modules`, and `ShortComplex`. It uses neither tensor-section constructors, local-freeness
properties, short exactness nor biproducts. Prune direct imports and import the modules supplying
the required statement infrastructure. The theorem signature, definitions and visibility are
unchanged. Its proof is equality substitution; no target meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
```

## New

```lean
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.Algebra.Homology.ShortComplex.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal | X3 | Own imports narrowed; unchanged signature; final proof and axiom probe compile. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparison | unclaimed | Sole direct importer. It explicitly imports every removed module itself, so its imports, statements and proofs require no adaptation. |

The only textual caller of the theorem is `DeterminantSplitComparison.lean`. Its signature and
all downstream signatures keep the same meaning. No consumer files are changed in this delivery.
The new public imports provide infrastructure already publicly accessible through the old
imports, including the same tensor instance from `Modules.Invertible`.

## Status

landed 20261014T042431-L-1212143 2026-10-14 (merge of deliver/X3/Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal)
