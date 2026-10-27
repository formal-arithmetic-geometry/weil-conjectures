# Unit realization scalar proof API

## Reason

Prove the existing realization theorem through its explicit coefficient isomorphism,
coefficient naturality of raw classes and Ext evaluation, and local scalar conjugation.
The new declarations expose these individual steps without changing existing statements
or definitions. In particular no scalar action is inferred from a bare additive isomorphism.

## Old

The six new modules and their declarations were absent. The existing theorem
`AlgebraicGeometry.Scheme.Modules.exists_unitRealizationScalar_of_coherentAction`
had its original signature and proof `:= by sorry`.

## New

The existing theorem has the identical signature and a proof combining the new coefficient
isomorphism and raw evaluation lemmas with its existing `ha` and `hl` hypotheses.
New modules:

- `Sheaf.AlgebraicGeometry.UnitStructureCoefficientIso`: explicit structural coefficient
  isomorphism and tensor-section scalar formulas.
- `Sheaf.AlgebraicGeometry.SheafHDerivedNaturality`: coefficient naturality of the fixed
  Ext evaluation map.
- `Sheaf.AlgebraicGeometry.UnitLocalizedScalarConjugation`: local scalar conjugation
  for the explicit coefficient isomorphism, before taking cohomology.
- `Sheaf.AlgebraicGeometry.UnitScalarRawData`: explicit raw coefficient transport.
- `Sheaf.AlgebraicGeometry.UnitCoherentRawEvaluationFormula`: the remaining evaluation
  compatibility step, as a named theorem with its source and proof in words.
- `Sheaf.AlgebraicGeometry.UnitScalarRawEvaluation`: coefficient class naturality and
  the passage from a raw scalar relation to coherent Ext multiplication.

Every construction is explicit. No witness is selected from a mere existence theorem.
No existing public import, declaration signature, definition or attribute changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UnitRealizationScalarNormalization | U2 | New private proof import; theorem signature and definitions identical. |
| Sheaf.AlgebraicGeometry.UnitAffineCohomologyEtaleRealization | unclaimed | Existing import and theorem application unchanged; no adaptation needed. |

The new modules have no pre-existing consumers. No target definition changes and no target
statement review is reopened.

## Status

landed 20261025T123943-L-1920510 2026-10-25 (merge of deliver/U2/Sheaf.AlgebraicGeometry.UnitRealizationScalarNormalization)
