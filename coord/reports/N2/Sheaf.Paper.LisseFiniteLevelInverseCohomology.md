## What changed

Filled `AlgebraicGeometry.Scheme.lisse_finite_level_inverse_realization_cohomology`
in `Sheaf.Paper.LisseFiniteLevelInverseCohomology`, preserving its entire signature.
The proof constructs the local derived comparison using the fixed-realization
pullback square, the canonical module pullback compositor, and the supplied local
markings. Exact functor homology comparisons give constant cohomology models.
Cover conservativity gives the original bounds; finite local models give local
constancy and finite geometric stalks.

Added only private proof imports for existing declarations. Both original public
imports are unchanged. Updated the item's DAG proof and dependencies to match the
Lean argument, including the fixed pullback and canonical composition tools. No
other existing module or node is changed, and no interface change record is needed.

The module compiled on the project server in 13.3 seconds after import cleanup
(8.0 seconds before cleanup). The delivery compiles it again with the
declaration/axiom probe. Static checks confirm an unchanged theorem signature,
zero textual holes and Lean lines of at most 100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.lisse_finite_level_inverse_realization_cohomology`
(node `new-lem-weil-pbc-lisse-inverse-realization-cohomology`).

There are zero holes left in the item and zero holes added by this delivery.
No new theorem is split off. This proves the item from existing stated dependencies;
in particular `lisseTower_localized_constants_model` remains an existing dependency
with its own proof obligation. This is not a claim that the full dependency closure
is already free of sorry.

## No longer needed

No existing module is withdrawn or pruned. Removed the redundant draft proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`, already publicly
available through the original imports. All remaining added imports supply named
proof declarations or instances used by the proof.

The standalone `constantAdicQuotientScalarComparison` theorem is not independently
applied: its constant-realization comparison is supplied by the existing
`lisseTower_localized_constants_model`. Its node remains a statement dependency,
and its module remains needed by existing definitions and dependencies; this is
not a module pruning claim. No other original proof dependency is discarded.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The original prose suggested choosing covering
arrows through points and refining by affine opens. `ProEt.mem_topology_iff` already
provides a covering presieve inside the given sieve, and its underlying scheme
family is exactly a proetalePrecoverage by `ProEt.mem_precoverage_iff`. This avoids
that extra refinement and retains the required fpqc condition, including empty
coverings. The original plan also left the fixed-realization pullback and derived
composition comparisons implicit; the DAG now records the existing declarations
actually used for them. The unit's statement and route are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.LisseFiniteLevelInverseCohomology": "9ae0db1373b5df3163eff31dbd61162fe38a1dbe"}, "results": {"Sheaf.Paper.LisseFiniteLevelEtaleModel": {"hash": "a1ec5c15ad67ec3e0a91e4e8b0b69910260c9388", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T16:05:47+0800", "transitive": 0, "version": 1}
```

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
