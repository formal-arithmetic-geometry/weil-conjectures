# normalization_in_finite_residue_field_extension

## Reason

The normalization module is used only by the proof, but was imported publicly. The
stage-3 brief requires a plain import in this case. Replace its public re-export with
public imports of the signature's integral-morphism and integrally-closed-ring types.
The theorem's signature, docstring, and all definitions remain unchanged. No target
statement changes or needs semantic re-review. This record is required by preflight
because the set of public imports shrinks.

## Old

```lean
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
```

## New

```lean
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | not changed by this delivery | Imports the item for its theorem; existing signatures use no normalization declaration. No adaptation needed. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | not changed by this delivery | Imports the item for its theorem; its current proof uses no normalization declaration. No adaptation needed. |

These are the two direct importers found by searching lean/Sheaf and by preflight.
Both import the item privately, have their own public Integral import, and have
no reference to the normalization-only API. The public theorem remains available
with exactly its existing type.

## Status

landed 20261012T060751-L-2913766 2026-10-12 (merge of deliver/Q1/Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension)
