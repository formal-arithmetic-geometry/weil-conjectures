## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one` by choosing
an affine neighbourhood at each point, applying the finite-complement lemma, the
construction of a globally generated invertible module, and the ample criterion. Added
the criterion module as an unclaimed repair: restored its theorem after changing its
proof-only import to the upstream `WeilConjectures.AlgebraicGeometry.AmpleIso`, where
`nonvanishingLocus_iso` now lives. The item imports the repaired criterion module.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_integral_dim_one` (1 of 1
sorries in the item). The repaired criterion module has no remaining sorries.

## No longer needed

None. All three planned dependencies are used. No DAG nodes or modules from the item's
proof plan were pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream sync had commented out `exists_isAmple_of_enough_globallyGenerated` because
its old proof-only import pointed at the retired Sheaf `AmpleIso` module and could not
resolve the private locus-isomorphism helper. The helper is available through the
upstream `WeilConjectures.AlgebraicGeometry.AmpleIso` import-all interface; restoring the
existing proof repairs the dependency without changing its statement.

## Forced adaptations

`lean/Sheaf/AlgebraicGeometry/ExistsAmpleOfEnoughGloballyGenerated.lean` is an
unclaimed dependency module adapted because its original source has the theorem
commented out and therefore cannot provide the declaration required by the item.
The original compiler error was `Unknown identifier nonvanishingLocus_iso` in the
commented theorem proof. The changed lines restore that existing theorem and replace
`import all Sheaf.AlgebraicGeometry.AmpleIso` by
`import all WeilConjectures.AlgebraicGeometry.AmpleIso`; the adapted module compiles
with the item.

The change is recorded in
`coord/changes/exists-ample-enough-globally-generated-repair.md`.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
