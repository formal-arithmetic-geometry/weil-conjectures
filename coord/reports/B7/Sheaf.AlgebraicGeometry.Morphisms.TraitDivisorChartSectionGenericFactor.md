## What changed

This is the assigned retirement repair. The duplicate Sheaf module is listed in
`deleted.txt`, and the DAG node now records the adopted upstream declaration. The direct
consumer `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionLocalizedRootChart`
was adapted to import
`WeilConjectures.AlgebraicGeometry.Morphisms.TraitDivisorChartSectionGenericFactor` and to
call its stronger theorem. The upstream `ε` witness is converted to the consumer's existing
`b` witness; the consumer theorem statement is unchanged. The migration compiles.

## Proved and sorry left

The retired module had no remaining `sorry`; it is withdrawn as an assigned retirement.
The adapted consumer has no `sorry`. No new declarations or holes were added.

## No longer needed

The Sheaf duplicate module and its private import of the Sheaf generic normalization
comparison are no longer needed. The upstream trait-divisor theorem supplies the same
conclusion and remains in the proof dependency route. No DAG proof dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The assignment is a retirement rather than a theorem-proof hole: the Sheaf declaration was
a duplicate after the upstream theorem was adopted. The original DAG proof route remains
valid after attaching this node to the upstream declaration; only the consumer interface
needed migration.

## Second reading by B7

The consumer was compiled against the upstream theorem. Its public statement and conclusion
are unchanged, and the upstream `ε` is used to reconstruct the required `b` map.

The interface retirement is documented in `coord/changes/retire-trait-divisor-chart-section-generic-factor.md`.
