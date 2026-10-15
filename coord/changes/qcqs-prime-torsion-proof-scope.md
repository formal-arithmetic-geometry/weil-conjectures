# AlgebraicGeometry.Etale.qcqs_higherDirectImages_prime_torsion

## Reason

The completed proof uses kernel subobjects, cocones and filtered colimits. Opening
CategoryTheory.Limits makes their names available in the item module. The delivery checker
classifies a changed open command as an interface change, so this record documents it.
A private divisibility order on the private PrimeAnnihilator structure supports the proof's
filtered index. No public statement, definition, public import or existing instance changes.

## Old

The scope command, verbatim:

```lean
open CategoryTheory
```

## New

The scope command, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
```

This changes name resolution within the file. The public theorem signature and all
five public imports are byte-identical. The added annihilator index, its order
instance and the two proved helper theorems are private implementation declarations.
No existing public definition, instance or declaration is changed or removed.

## Users

Re-ran `tools/downstream.py Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion --uses
qcqs_higherDirectImages_prime_torsion` during the second reading. It lists the fourteen
modules below; the only textual occurrence of the theorem is its own declaration.
Holders below are those recorded in this checkout at the second reading. No downstream
source is changed or needs adaptation, regardless of its current holder.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange` | B2 | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange` | A4 | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients` | unclaimed | None; public interface unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization` | unclaimed | None; public interface unchanged. |
| `Sheaf.Targets.EtaleSmooth` | C1 | None; public interface unchanged. |
| `Sheaf.Targets.EtaleSmoothRing` | A2 | None; public interface unchanged. |
| `TargetsCheck` | unclaimed | None; public interface unchanged. |

## Status

landed 20261015T154207-L-163402 2026-10-15 (merge of deliver/E4/Sheaf.AlgebraicGeometry.QcqsHigherImagesPrimeTorsion)
