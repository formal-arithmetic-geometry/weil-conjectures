# AlgebraicGeometry.Scheme.Modules.scalarCohomologyExtMap_smul proof scope

## Reason

The proof requires constructing scalar multiplication on the structure sheaf and specializing
an Ext identity across two smallness universes. The static interface checker conservatively
reports changes to the universe command and section-local reducibility commands. These commands
change proof elaboration only. All existing signatures, public imports, definition bodies,
visibility, and global attributes remain identical. No target meaning changes and no target
statement review is reopened. There are no forced adaptations.

## Old

```lean
universe u
```

There are no local irreducibility registrations on `scalarMap`, `scalarUnitLinear`, or
`scalarSheaf`. The private scalar endomorphism and generic Ext helper are absent.
The existing local attributes and section boundaries are unchanged.

## New

```lean
universe u w w' v v' u' t
attribute [local irreducible] scalarMap scalarUnitLinear
attribute [local irreducible] scalarUnitEndomorphism
attribute [local irreducible] scalarSheaf
```

The extra universes are used only by the private generic Ext lemma. The public declarations
still use exactly their original universe `u`. The local attributes occur within the existing
section beginning before `constantScalarUnit` and end at its existing `end`, before the original
global irreducibility command. `scalarUnitEndomorphism` is private; it is a real construction via
`unitHomEquiv` and compatible scalar sections, with no unproved data. The other four private
helpers have complete proofs. Local transparency options are attached to individual helper
lemmas or confined to proof blocks, and are not exported. No existing instance or elaboration
attribute escapes the section. No public definition body changes.

## Users

The table lists the item and all direct importers found by a read-only anchored import search
across both library roots. Holder values are from the current claim records. The local
attributes do not escape the section; direct importers therefore see identical definitions,
statements, global reducibility, and instances. All further transitive importers are unaffected
for the same reason. No consumer changes are delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRectangleProjectionSectionsTensor | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalCupZeroGlobalSections | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ExternalTensorAffineOpenSections | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | C3 | Local proof elaboration only; identical exported interface. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAcyclic | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComparison | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechComplexes | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsAffineLocalCohomology | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsDirectImages | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproduct | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCoefficientsPushforwardCoproductComparison | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupScalarComparison | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupZeroTensor | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalRightCechModels | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardKunnethResolutionModel | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardScalarAffineSectionsExact | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupDegreeZero | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageFirst | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarGlobalSectionsComparison | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarInverseImageCompositionCoherence | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPullbackTensorCoefficient | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarTensorGlobalSectionsMorphism | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitClassPullback | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyCoordinates | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackComparison | unclaimed | Unchanged signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality | unclaimed | Unchanged signatures and data; no adaptation. |

## Status

landed 20261013T172651-L-2098125 2026-10-13 (merge of deliver/C3/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
