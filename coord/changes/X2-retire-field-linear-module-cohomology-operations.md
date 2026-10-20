# AlgebraicGeometry.Scheme.Modules field-linear module cohomology operations

## Reason

Retire the assigned Sheaf copy in favor of its adopted source-library twin, as directed
by coord/retire-items.tsv and the human's hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The original has zero proof holes.
A complete source diff shows identical public signatures, attributes, imports,
definition bodies and theorem proofs. Differences are only the copyright header,
blank lines, and five locally named instances. Their values are unchanged.

One consumer initially compiled in 27.8 seconds, then exceeded 60 seconds during
preflight. Scratch comparisons isolated the costly coefficient-map and normalization
elaboration: imports alone took 5.3 seconds, the first definition 3.4 seconds, and the
coefficient-map prefix 27.3 seconds. Keeping the coefficient and cohomology-group
definitions locally irreducible during the normalization definition, then restoring
them where conversion is required, gave a successful scratch compile but the delivery
compile still timed out. Inferring the mapped component equality and explicitly
unfolding CoherentEtale.Coeff at its two applications fixed the delivered file too.
These local attributes change elaboration only: every public definition body and
signature remains verbatim, and no global reducibility attribute changes.

All seven current direct consumers now import the official library module. The three
DAG attachments move to it. The upstream module and target statements are untouched.
No mathematical definition or theorem statement changes, so this is a duplicate-module
retirement rather than a proof or decomposition. No additional target semantic review
is triggered: the full data constructions are retained verbatim in the adopted twin.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The 1,265-line Sheaf module duplicated the official library's declarations, including
scalarMap, scalarSheaf, scalarCohomologyExtEquiv, scalarCohomologyPullback,
scalarCohomologyCup and externalCup. Its three DAG lean attachments named the Sheaf module.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The duplicate file is withdrawn using deleted.txt. Its declarations remain available
with exactly the same fully qualified names in the adopted twin. All consumers switch
their single import, and the three DAG attachments name the twin. Two pre-existing
long local-instance lines are wrapped to satisfy the delivery's 100-character rule.
CanonicalCoherentEtaleComparison also caches five existing definitions locally:
coherentEtaleMap, CoherentEtale.IsNormalized, CoherentEtale.sourceGroup,
CoherentEtale.targetGroup and CoherentEtale.Coeff. The coefficient/map definitions
are restored before the comparison proof; sourceGroup and targetGroup are restored
before the later Ext/derived-functor conversions. In the existing uniqueness proof,
hm is inferred by congrArg applied to the upstream component characterization.
The two applications of hm explicitly unfold CoherentEtale.Coeff. This is the same
argument with targeted conversions; the delivered module compiled in 33.1 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.GenusWellDefined | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.ScalarCupPositiveResolutionClassCompatibility | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImageSecond | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |
| Sheaf.AlgebraicGeometry.ScalarTensorUnitCoefficient | unclaimed | Replace the duplicate import by the twin; identical declarations and data. |

The table is the complete output of tools/downstream.py for the original module.
A recursive source import-closure check after substitution found zero Sheaf/WeilConjectures
twin pairs in each of these seven consumer environments. Both prerequisite twins,
ModuleResolutionHomologyExt and RingedSpaceModuleCohomology, were already adopted.
The blueprint unit sk-prop-av-cube and its mathematical proof route are unchanged.

## Status

landed 20261020T145551-L-2413903 2026-10-20 (merge of deliver/X2/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
