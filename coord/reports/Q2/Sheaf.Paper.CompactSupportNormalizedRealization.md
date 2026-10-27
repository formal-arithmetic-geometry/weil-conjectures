## What changed

Reduced `WeilConjectures.coefCompactSupportInput_properties` to the strictly smaller
completed-tower comparison `WeilConjectures.compactSupportInput_completed_tower` in
new module `Sheaf.Paper.CompactSupportInputTowerCompatibility`.

The parent proves its identity and cocycle conjuncts: the evaluation isomorphisms of
the native coefficient-system reduction conjugate its transitions to the specified
input maps, and the existing sequence transition calculus gives both equations.
The third conjunct is the remaining comparison with `sfIntegralReductionTower`.
All existing public statements and definitions are unchanged. The new import is private.
Both modules compiled through `lcompile.py --all`.

## Proved and sorry left

Closed the original hole `WeilConjectures.coefCompactSupportInput_properties`
(node `lem-coef-compact-support-normalized-realization`) by a genuine decomposition:
two conjuncts are proved, and the third is split off. Added one hole,
`WeilConjectures.compactSupportInput_completed_tower`
(node `lem-coef-compact-support-input-tower-compatibility`). No hole remains in
the item module; the delivery has one hole overall. Net holes closed: zero.

The repository synchronized the earlier M4 landing during initial reading. Its proofs
of `coefCompactSupportQuotient_eq`, `coefCompactSupportTau_adjacent`, and
`compactSupport_normalized_realization` are preserved and not counted as Q2 proofs.

## No longer needed

No existing imports, nodes or modules removed. No new K-flat construction is introduced.
The parent uses the native coefficient-system calculus for its first two conjuncts.

## Where the brief, the DAG or earlier work was wrong

The initial module snapshot had four holes, but the synchronized M4 landing had
already closed three. The existing DAG recorded the remaining input-properties hole;
this delivery replaces that step with the compiled decomposition.

The direct full-proof attempt exposed a mismatch when transporting the normalized
completed restriction compositor to scalarReductionDerivedRestriction. These functors
agree by unfolding their definitions, but the opaque completed-limit representation
prevents the attempted direct elaboration. The remaining theorem records that exact
comparison problem, including the adjacent-map argument and induction. Its edge cases
are identity quotients, zero K, and the empty scheme; the argument uses no finiteness.

## New nodes

`lem-coef-compact-support-input-tower-compatibility` carries only the comparison of
restricted direct input reduction maps with the recorded integral reduction tower.
Its statement is the third conjunct, strictly smaller than all input properties and
than the realization theorem. Its docstring and DAG give the native-system restriction
comparison, the scalar-adjunction calculation for adjacent levels, and induction on
the index difference. There are no definition changes or change records.

Preflight initially detected a cycle through the compact-support operation nodes in
the new node's planned proof dependencies. The plan now uses the scalar adjunction
directly to identify the input transition, retaining the safe coefficient calculus
and normalized K-flat comparison dependencies. No compact-support operation is
needed for this scalar input comparison.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
