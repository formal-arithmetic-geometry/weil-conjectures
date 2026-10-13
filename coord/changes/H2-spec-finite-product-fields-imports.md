# AlgebraicGeometry.spec_finite_product_fields

## Reason

Correct proof-only public imports and remove redundant direct imports.
`Restrict` provides the objects in the unchanged theorem statement; `Limits`
is needed only by the proof, for the projection open-immersion instance.
No definition or declaration signature changes, and no target review is reopened.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Limits
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SpecFiniteProductFields --names`
listed the following modules. The sole direct importer privately imports the
changed module and compiles unchanged against the final sandbox module. Its
statement does not use any newly hidden definition. Its downstream modules thus
see the same public interface. No adaptation or edit of another module is needed.
Holders below reflect the local claims snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.OpenCurveBoundaryHigherDirectImageVanishing | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.AlgebraicGeometry.EtaleFibreSpecialization | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.AlgebraicGeometry.StrictHenselizationDVR | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.RingTheory.Etale.LocalDimension | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.RingTheory.Etale.QuasiFiniteAtPrime | unclaimed | Compiles unchanged; private import only. |
| Sheaf.RingTheory.HenselianFiniteEtaleEquivalence | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.RingTheory.HenselianFiniteEtaleFieldLift | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.RingTheory.StrictHenselizationDimension | unclaimed | No effect through the direct importer’s private import. |
| Sheaf.RingTheory.StrictHenselizationRegular | unclaimed | No effect through the direct importer’s private import. |

## Status

landed 20261013T054218-L-443221 2026-10-13 (merge of deliver/H2/Sheaf.AlgebraicGeometry.SpecFiniteProductFields)
