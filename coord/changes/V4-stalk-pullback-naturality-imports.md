# AlgebraicGeometry.SingleComplexBaseChange.comparisonIntoPullback_naturality

## Reason

Restore the quarantined module assigned in coord/rework.tsv. Compiling its
unmodified archive reproduces the duplicate AlgebraicGeometry.derivedPullback
error from its old private Sheaf.AlgebraicGeometry.DerivedPullback import.
The shared upstream stalk-transport dependency already supplies the canonical
derived pullback. Remove that obsolete import and the other redundant private
imports. Explicitly export Sheaf.Algebra.Homology.KFlat, which defines the
IsAcyclicTensorKFlat predicate in the existing public theorem signature.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison
import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Sheaf.Algebra.Homology.KFlatStalkCriterion
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.StalkComparisonSourceTransport
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparison
```

The entire module after the imports is verbatim from the quarantine archive:
comparisonIntoPullback has the same constructed value, and
comparisonIntoPullback_naturality has the same signature and complete proof.
No definition, hypothesis, conclusion, instance, source-library file, DAG route,
or target meaning changes. The three declared proof dependencies remain in use.
The added public import exposes an existing predicate rather than defining it.
The removed model, pullback and stalk-condition imports are obsolete Sheaf twins;
the canonical declarations already come from the public upstream stalk transport.
KFlatStalkCriterion is used inside the retained extension-comparison dependency,
not directly by this proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality | V4 | Restored with corrected imports. |
| Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpectrumComparisonSourceTransport | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenComparisonIntoPullbackTransport | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCanonicalSquare | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonCore | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenRestrictedComparisonTransport | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenCoordinateStalkTransportData | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenTermwiseComparison | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |
| Sheaf.AlgebraicGeometry.TensorStalkFixedMapSquare | quarantined; no local claim record | Unchanged declaration signatures and bodies; no adaptation. |

A source search of lean/Sheaf and quarantine/Sheaf finds precisely the ten
archived direct consumers above. Their existing references still use the same
names, K-flat hypotheses and comparison formula. No consumer is changed or
withdrawn; their separate quarantine assignments remain. The source-library
parallel module and its consumers remain untouched. tools/downstream.py with
--allow-missing --uses reports zero live downstream modules and zero live uses
of the currently quarantined item.

Validation: the repaired module compiles through lcompile.py without diagnostics
in 12.3 seconds. A separate module importing only this module publicly restates
its entire theorem signature and proves it by the original theorem in 3.3
seconds. Both comparisonIntoPullback and comparisonIntoPullback_naturality have
only propext, Classical.choice and Quot.sound in their printed axiom lists.
No direct or inherited sorry remains in either declaration on that build.

## Status

landed 20261020T174915-L-819484 2026-10-20 (merge of deliver/V4/Sheaf.AlgebraicGeometry.StalkComparisonPullbackNaturality)
