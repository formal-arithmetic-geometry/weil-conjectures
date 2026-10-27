# AlgebraicGeometry.Etale.bijective_moduleSpecialization_of_abelianIso

## Reason

Restore the item preserved at the quarantine path in coord/rework.tsv. The live
item source is absent. Its archived proof is complete, but its specialized
strict-henselization restriction API and derived coefficient comparison import
have been retired. Earlier A3 repairs of the dependencies are already in the
live tree; this delivery restores only the missing item against those interfaces.

The theorem signature, private helper signatures, docstrings, module-stalk
specialization construction, and strict-local abelian specialization are preserved.
No definition or theorem statement is changed. No upstream source module is edited.

## Old

Archived import:

```lean
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
```

Archived proof uses:

```lean
(Etale.existsUnique_strictHenselizationStalkRestriction s G)
Etale.strictHenselizationSectionRestriction
Etale.strictHenselizationNeighbourhoodSection s j
strictHenselizationStructuralMap_eq s j.unop
```

## New

Replacement import:

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
```

The same moduleAbelianForget abbreviation is provided by its canonical upstream
module. The proof now uses:

```lean
((Etale.strictLocalSectionCone s).existsUnique_restriction G)
Etale.PointedEtaleSectionCone.restriction
Etale.strictLocalNeighbourhoodSection s j
((exists_strictHenselizationStructuralMap s).choose_spec j.unop)
```

An explicit change of the local restriction equation exposes its pointed affine
neighbourhood, so rewriting does not need to unfold the abstract diagram. The
structural-map leg rewrite ends with rfl to identify the chosen structural map.
All germ equations and the colimit argument remain the archived proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso | D3, this item | Restore the archived complete proof and adapt its API calls. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | quarantined; not adapted | Its call in prime_invertible_constructible receives the identical theorem signature and the identical specialization maps. |

The source-only downstream tool reports the item as unknown because it is absent
from lean/. Searches of both library roots find no live importer. Searching
quarantine/Sheaf finds the direct parent above; its call was read at lines 212-214.
Searching dag/nodes finds the same parent still lists this item as a dependency;
the item is therefore restored, never withdrawn. No consumer needs an adaptation.
A temporary Lean consumer probe applies the restored theorem with all original
parameters. A separate rfl probe checks that strictLocalSpecialization is still
etaleStalkSpecialization. Both probes are excluded from the delivery.

## Status

landed 20261022T032516-L-2033787 2026-10-22 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ModuleSpecializationAbelianIso)
