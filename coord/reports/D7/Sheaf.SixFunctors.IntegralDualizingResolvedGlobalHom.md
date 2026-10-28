## What changed

Proved `WeilConjectures.integralDualizing_resolved_globalHom` in the assigned module,
without changing any existing statement, definition, attribute, or public import.
Added private, proved `scalarSectionsEquiv` and `scalarSectionsIso`: a unit-module
morphism is sent to its value at 1 on the final pro-etale object, and the inverse
extends a terminal section by restriction. The equivalence is linear for the exact
`integralDualizingScalarSections` action in the statement.

Used the first comparison of `derived_internalHom_sections_model` for the fixed
K-injective target. The derived-sections unit is inverted on every sheaf Hom complex
by resolving its source with a K-flat complex. On the K-flat model the Hom complex
is K-injective; both horizontal arrows in the naturality square are isomorphisms.
For ordinary scalar sections this uses the existing sectionwise quasi-isomorphism
at the final object, reflected by the exact forgetful functor to abelian groups.
Single-file server compilation passed cleanly in 26.3 seconds.
All added imports are private proof imports. Updated the existing node's proof,
proof dependencies, and proof origin to record these actual uses.

Searches: LeanFinder returned generic Hom-complex/K-injective cohomology results;
Loogle had no registered declaration for the project-specific derived-sections unit;
Mathlib grep returned no ready-made integral scalar comparison. The library already
provides the substantive internal-Hom, K-flat, and sectionwise invariance theorems,
so no new public statement was necessary.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.integralDualizing_resolved_globalHom`
(node `lem-coef-integral-dualizing-resolved-global-hom`).
The assigned module has zero remaining `sorry`s. Added zero holes and zero split-off
statements. Both private section-identification helpers are fully proved.

## No longer needed

No imports removed, no existing nodes or modules withdrawn. All originally declared
dependencies remain used. The proof needs no separate integral coefficient-model
obligation, no inverse-limit comparison, and no new scalar refinement of the
sections-model theorem. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is valid. Its second step needs the independent-universe
K-flat resolution, K-injectivity of Hom, sheaf-Hom quasi-isomorphism invariance, and
sectionwise quasi-isomorphism declarations explicitly; these are now listed in the
node. The additive sections theorem alone does not establish the specified integral
module comparison, so the proof supplies the linear terminal-sections identification
and reflects quasi-isomorphisms through the exact scalar-forgetful functor.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingResolvedGlobalHom": "343c2ecd7ad9e87fc68517f9c10ebc5fb49bbf87"}, "results": {"Sheaf.SixFunctors.IntegralDualizingResolvedMappingLimit": {"hash": "6c4df763408ff3346ecb77e08e115f9e9b095d31", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T14:13:33+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
