## What changed

Proved `WeilConjectures.pointIntegralPerfectRealization` in
`Sheaf.Paper.PointIntegralPerfectRealization`, preserving its full signature,
existing docstrings, and public import. Added proof-only imports of
`Sheaf.Paper.PointExactExtensionSections` and
`Sheaf.Paper.PointSectionsReconstruction`. The latter uses `import all` to reuse
its proved private homology comparison for the standard and small module-derived
categories.

The proof specializes the existing exact extension adjunction to integral
coefficients and applies the forward integral reconstruction result. It transports
bounded finite cohomology across `ShrinkHoms.equivalence`, compares the two derived
sections functors through their localization factorizations, and restricts the
adjunction along fully faithful inclusions. The restricted unit is invertible by
reflection of isomorphisms. This is a proof for the specified fibre functor.
Updated only this theorem's DAG node to describe that route. No definitions,
other existing modules, or target statements change.

## Proved and sorry left

Closed the sole original hole in
`WeilConjectures.pointIntegralPerfectRealization`
(node `lem-weil-point-integral-perfect-realization`): 1 of 1 holes proved.
No `sorry` remains in the item; no holes or split-off statements were added.
Both reused theorems already have complete proof bodies. Their existing
transitive dependencies are retained, with no claim here to have proved them.

## No longer needed

No existing import was removed and no module is withdrawn. The former detailed
construction is replaced by the two existing general point theorems, so these
nodes are no longer direct proof dependencies of this item:

- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-continuous-coefficients-immersion-restriction`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `lem-weil-pbc-constant-module-section-properties`
- `lem-weil-point-proetale-sections-exact`
- `def-weil-pbc-constant-sheaf`
- `def-pur-sheaf-tensor-product`
- `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-sp-exact-functor-preserves-homology`
- `lem-weil-pbc-unbounded-derived-iso-cohomology`
- `lem-sc-noetherian-finite-module-finite-presentation`
- `def-weil-point-finite-cohomology-complexes`
- `lem-weil-pbc-finite-free-resolution-noetherian`
- `lem-sc-dvr-fg-torsionfree-free`
- `lem-sf-perfect-cohomology-assembly`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `def-weil-derived-complete-integral-detailed`
- `lem-weil-point-sections-finiteness`

`def-weil-point-fg-complete-complexes` remains a direct dependency. Several of the
removed direct edges remain needed transitively by the general theorems or by
the statement; this delivery does not claim those modules can be withdrawn from
the library. There are no new nodes and no library modules pruned.

## Where the brief, the DAG or earlier work was wrong

The planned direct construction is unnecessary because the existing exact
extension and reconstruction theorems already provide its mathematical content.
Their standard module-derived category has a larger Hom universe than the
Grothendieck model in the target; a direct application would miss this difference.
The proof explicitly transports both homology and the derived right adjoint
across the canonical equivalence before restricting the adjunction. The unit's
realized proof-step list is empty, so no prescribed unit proof step is bypassed.
The original statement and its mathematical meaning are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PointIntegralPerfectRealization": "b3ad3af606170b6292573947ded1b34e384870ff"}, "results": {"Sheaf.Paper.PointFibreEquivalence": {"hash": "9eb31e7bb866f30e9d7e182c891a7e8e9cc326ff", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T14:11:33+0800", "transitive": 0, "version": 1}
```

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
