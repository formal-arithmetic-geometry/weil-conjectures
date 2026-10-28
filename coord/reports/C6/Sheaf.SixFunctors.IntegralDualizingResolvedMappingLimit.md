## What changed

Reduced the resolved mapping-limit comparison to its strict sequence-site mapping-tower
comparison, before applying any inverse limit. The original theorem signature and both
original definitions are unchanged. All added imports in the item are private proof imports.

The item now proves the inverse-limit part: injective tower terms have split successor
transitions; postcomposition gives split maps on each degree of the product Hom complex;
global sections preserve these splittings. The kernel of one minus shift is the ordinary
limit, and its inclusion into the shifted Roos cone is a quasi-isomorphism. The normalized
Roos comparison identifies this inclusion with the canonical right-derived-limit unit.
Whiskering that unit and the strict tower comparison gives the required natural isomorphism
in every source complex, rather than only objectwise isomorphisms.

To avoid expanding the full transpose comparison inside the final composition, the proved
identity-on-components comparison is a private irreducible definition in the item. Local
irreducibility attributes keep large section and derived functors behind their interfaces;
these attributes change no importer-visible declaration.

The new cochain-tower definition composes the existing global Hom complexes with the
source library's proved `HomologicalComplex.functorEquivalence.inverse`, including their
differentials and maps. This replaces an expanded hand-written transpose by the existing
construction and makes the transpose comparison definitionally the identity. No data is chosen from an unproved
existence theorem. No adopted source-library file is changed.

Validation: both sandbox modules compiled in import order; the profiled item compile
completed in 29.8 seconds and the new module in 6.7 seconds. Profiling options were then
removed for the delivery's required compile and preflight.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.integralDualizing_resolved_mappingLimit` (one of one item holes).

Added one hole, in the new module's public theorem
`WeilConjectures.integralDualizing_resolved_mappingTower`.
Its proof is exactly `by sorry`; its docstring and DAG node specify the source and complete
mathematical argument. This is a decomposition, with one hole closed and one added, net zero.
The new obligation has no inverse-limit conclusion and needs only K-injectivity, not the
original degreewise injectivity hypothesis. The complete ordinary-versus-derived-limit
argument stays proved in the item, so the new obligation is strictly part of the original
argument, not the same statement renamed. No other holes are added.

## No longer needed

The item no longer needs the planned dependency
`lem-sfb-global-rhom-resolved-tower-models`, module
`Sheaf.Algebra.Homology.RingedSiteGlobalRHomResolvedTowerModels`: its pointwise triangle
comparison is replaced by the canonical natural derived-limit unit and the proved Roos
kernel calculation. Its file and declarations are retained for any other consumers.

No original public imports are removed. The original scalar-model and internal-Hom/sections
nodes remain needed by the strict mapping-tower step; they are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan did not isolate the naturality of the mapping-tower identification
from the inverse-limit computation. The stated resolved-tower-model theorem supplies
pointwise models and triangles, but not the canonical natural comparison of the entire
functors used by this item. The delivery proves that latter limit comparison explicitly,
and records only the sequence-site identification as the remaining obligation.

The new statement includes zero source and target complexes. Exact equivalence preserves
K-injectivity, evaluation has exact left adjoints, and the K-flat replacement comparison
uses canonical unit naturality; none of these steps requires termwise injectivity. That
stronger hypothesis is used precisely in the proved split-transition limit calculation.
No target statement or existing shared definition is changed.

The generic tools used for the proved limit calculation are the existing kernel-to-shifted-cone
comparison, Hom-complex projections, split transitions of injective sequential towers, and
normalized Roos comparison. Their nodes are listed in the updated proof dependencies. These
are tools from other units: the original unit has no specialized statements exposing those
chain maps or their normalization. The unit record has no realized steps bypassed here.

Read the current server queue, rework table, return file and build-error path: the item is
listed as a stage-3 proof item with one hole; no rework or return entry and no build-error
file is present. The source-library boundary is respected throughout.

## New nodes

`lem-coef-integral-dualizing-resolved-mapping-tower`, realized by
`Sheaf.SixFunctors.IntegralDualizingResolvedMappingTower` and
`WeilConjectures.integralDualizing_resolved_mappingTower`.
It records the strict global Hom cochain model, its integral scalar action and naturality
before taking inverse limits, with the existing scalar-model and internal-Hom/sections
dependencies. The item's proof, proof dependencies and proof origin now follow the Lean
argument.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingResolvedMappingLimit": "ef461167162dc5297251039414b28726d7b84f24", "Sheaf.SixFunctors.IntegralDualizingResolvedMappingTower": "7173ac97d2c63063f0383b1f286aea8f4ceee988"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitCanonical": {"hash": "2ae9fac33d95b952ebd26062a5c95d0dc9c20b75", "status": "INFRA"}}, "seconds": 133, "time": "2026-10-28T14:36:33+0800", "transitive": 0, "version": 1}
```

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
