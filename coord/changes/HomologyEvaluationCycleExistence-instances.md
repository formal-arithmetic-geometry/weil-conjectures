# Local monoidal instances in HomologyEvaluationCycleExistence

## Reason

The proof uses the existing sheaf tensor, symmetry, and closed structure. These local
instances are required for typeclass inference in the helper proofs; their registration is local to the module and no existing public declaration changes.

## Old

The item module contained only the target theorem with `sorry` and no proof-only imports
or local instances.

## New

The item module contains three private noncomputable structure definitions, one each for
`MonoidalCategory X.Modules`, `SymmetricCategory X.Modules`, and `MonoidalClosed X.Modules`,
all defined from the established `SheafOfModules` constructions. The second reader changed
the candidate private global instances to private definitions registered using
`attribute [local instance]` to prevent downstream typeclass registration.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomologyEvaluationCycleExistence | G4 | proof uses the local instances |

The local instance registrations end with the module; no other module requires adaptation.

## Status

landed 20261013T190140-L-3216235 2026-10-13 (merge of deliver/G4/Sheaf.Algebra.Homology.HomologyEvaluationCycleExistence)
