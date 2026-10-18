## What changed

Proved `AlgebraicGeometry.weaklyEtale_stability` in
`Sheaf.AlgebraicGeometry.WeaklyEtaleStability`, preserving its exact signature.
The first four conjuncts use Mathlib's existing stability and locality instances;
the over-base conjunct uses `WeaklyEtale.of_comp` after rewriting the commuting
triangle. The last two conjuncts use the already proved source-library
`proAffineEtale` composition and affine base-change instances.

Removed the public import `Sheaf.RingTheory.IndPrincipalZariski` and the proof-only
import `Sheaf.RingTheory.IndEtaleStability`. The sole remaining import,
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`, supplies all notions
and instances actually needed. Updated the existing node's proof, proof dependencies,
proof origin and obsolete tool approval to describe this direct reuse.

Validation: the original-import version and the pruned version both compiled on
the project server in about three seconds. A separate `#print axioms` check reports
only `propext`, `Classical.choice` and `Quot.sound`. No diagnostic command remains
in the delivered source. `tools/downstream.py` lists 32 downstream modules and zero
uses there of `Algebra.IsIndPrincipalZariski`, the definition whose reexport is removed.
No target, definition or theorem statement changes; no consumer adaptation is needed.
The public-import pruning is recorded in
`coord/changes/weaklyEtale-stability-prune-imports.md`, with every downstream module
and its current holder listed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.weaklyEtale_stability`
(node `sk-lem-pe-weakly-etale-stability`). Original holes: 1; remaining holes: 0;
new holes: 0. This is a complete proof from already proved declarations, not a
decomposition. Its axiom check does not contain `sorryAx`.

## No longer needed

Removed imports:
- `Sheaf.RingTheory.IndPrincipalZariski`: the statement uses neither principal
  ind-Zariski algebras nor their extra API.
- `Sheaf.RingTheory.IndEtaleStability`: the exact scheme stability instances already
  exist in the source library; no separate bundled ring stability theorem is needed.

Removed direct proof dependencies:
- `def-pc-fibre-product`
- `def-weil-flat-morphism`
- `def-weil-open-immersion`
- `def-weil-pbc-ind-etale-algebra`
- `lem-pc-flat-compose`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `lem-weil-pbc-flat-morphism-base-change`
- `lem-weil-pbc-ind-etale-stability`

The existing Mathlib/source proofs encapsulate these lower-level constructions and
facts. In particular, the source composition instance already uses
`RingHom.IndEtale.comp`; its base-change instance works directly with the affine
etale stages of the pro-presentation. Removed the obsolete top-level `tool_uses`
entry `lem-weil-pbc-ind-etale-stability`. This prunes the separate bundled theorem,
including its unrelated principal ind-Zariski clauses, from this item's direct route.
The unit's statement and all its scheme-level stability, locality and over-base
clauses remain intact. No assertion is made that these dependencies are unused by
other modules or by the internals of the reused source proofs.

## Where the brief, the DAG or earlier work was wrong

The old proof plan expanded stability results that are already completely proved
in the pinned Mathlib and source library. Reusing their exact instances closes all
seven conjuncts without new intermediate theorems. The source base-change instance
requires `IsAffineHom f`, which follows from the existing affine hypotheses in the
unchanged theorem statement. The source composition instance is stronger than the
affine-only clause requested here. No mathematical statement was disputed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
