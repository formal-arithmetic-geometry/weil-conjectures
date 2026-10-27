## What changed

Restored the returned proof of `Sheaf.SixFunctors.CoefQbarVerdierInternalHom`.
The item module now imports two proof-only split components and proves
`WeilConjectures.CoefQbarVerdier.internal_hom_descent` by constructing
`InternalHom` from their comparison and universal-property results. The existing
finite-stage declarations remain unchanged. The two split component modules and
matching DAG nodes are restored because the prior delivery's dependency modules
were removed during the build rework quarantine.

## Proved and sorry left

Closed the item's one existing `sorry`,
`WeilConjectures.CoefQbarVerdier.internal_hom_descent`. The existing
`commonStageHomPairs_all` and `finite_evaluation_transpose_bijective` declarations
remain proved. Added two strictly smaller named split-off statements, each with
one `sorry`:

- `WeilConjectures.CoefQbarVerdier.internal_hom_comparison_exists`, node
  `lem-coef-qbar-verdier-internal-hom-comparison`;
- `WeilConjectures.CoefQbarVerdier.internal_hom_universal_of_comparison`, node
  `lem-coef-qbar-verdier-internal-hom-universal`.

No definition contains `sorry`.

## No longer needed

None. The proof uses the finite coefficient data through the two split components;
no existing proof dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The earlier Y2 delivery had the correct constructor proof but its two new
component modules were lost when the red-build rework moved the item into
quarantine. This delivery restores those modules and records them in the item's
proof dependency graph. The item's target statement and the unit route are
unchanged.

## New nodes

`lem-coef-qbar-verdier-internal-hom-comparison` states the finite-origin natural
comparison descent. `lem-coef-qbar-verdier-internal-hom-universal` states descent
of the evaluation transpose after choosing that comparison. Both are in
`dag/nodes/sec-six-functors/` and are stated by the corresponding new modules.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
