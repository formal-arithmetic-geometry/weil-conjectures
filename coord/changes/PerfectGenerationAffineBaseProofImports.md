# Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase public imports

## Reason

The statement of `AlgebraicGeometry.perfectGeneration_affine_base` uses an
explicit shifted-Hom vanishing criterion, and its proof uses no declaration of
`Sheaf.CategoryTheory.WeakTriangulatedGenerator`. Remove the unused public import.
The existing theorem's name, signature, universes, and visibility remain identical.
No definition changes. The only visibility change is removal of the incidental
re-export of the weak-generator definitions.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.CategoryTheory.WeakTriangulatedGenerator
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KoszulAffineDetection | unclaimed | Direct importer; no use of either weak-generator declaration; signature unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectGeneratorExists | unclaimed | Direct importer; its own public import of WeakTriangulatedGenerator supplies those definitions; signature unchanged; no adaptation. |

No module is adapted. No target statement or definition used by a target changes.
Removing this import does not alter the elaborated types of the existing declarations.

## Status

landed 20261013T003158-L-2429093 2026-10-13 (merge of deliver/J1/Sheaf.AlgebraicGeometry.PerfectGenerationAffineBase)
