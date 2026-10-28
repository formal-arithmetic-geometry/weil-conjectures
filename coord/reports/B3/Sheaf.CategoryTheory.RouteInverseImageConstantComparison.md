## What changed

Replaced the original hole by the constant-set comparison, pointwise ring-operation check, and
natural ring-sheaf assembly. The set comparison is proved using global sections represented by
the constant singleton sheaf, the given adjunction, and uniqueness of left adjoints. It is natural
in all set maps. `constantRingSetComparison` conjugates it by `constantCommuteCompose`, with
naturality proved explicitly. The constant-section clause is proved by factoring through the
singleton sheaf and applying naturality to the function selecting the chosen constant.

`constantRingComparisonAssembly` constructs the ring-sheaf morphisms sectionwise from their four
operation identities, reflects their underlying isomorphisms, and proves naturality using `enat`.
The remaining operation check for a single constant ring is a named theorem in its own module.
`RingInverseImage` is extracted there verbatim and publicly re-exported by the item, to avoid an
import cycle. No existing consumer is edited. The original theorem signature and all original
public imports are preserved.

Change record: `coord/changes/B3-constant-comparison-ring-record-extraction.md`.

Validation: all five delivery modules compile cleanly through `lcompile.py`; the unchanged direct
consumer `Sheaf.CategoryTheory.GeometricRingInverseImage` also compiles against them (7.3 s).
The temporary consumer copy was removed. The original theorem signature was compared using the
project declaration parser and is unchanged. All five DAG Lean records match their source.

## Proved and sorry left

Original holes closed: `CategoryTheory.inverseImageConstantComparison` (one).
New holes added: `CategoryTheory.constantComparison_ring_operations` (one), node
`lem-route-inverse-image-constant-ring-operations`.
This is a decomposition, with net hole reduction zero, not a complete proof of the original item.
The remaining lemma concerns only four sectionwise identities for one ring and one lift, with
no ring functor, no `enat`, no adjunction, no natural ring isomorphism to construct, and no
constant-section normalization conclusion. Its docstring and node give the operation argument.

Proved helpers: `CategoryTheory.canonicalConstantSetComparison`,
`CategoryTheory.canonicalConstantSectionComparison`, and
`CategoryTheory.constantRingComparisonAssembly`.
`CategoryTheory.constantRingSetComparison` is a real construction with no postponed data.
There is no `sorry` in the item or in any definition.

## No longer needed

The explicit coproduct construction and the direct dependency
`lem-weil-pbc-left-adjoint-preserves-colimits` are replaced by the global-sections/adjunction
argument. Its obsolete `tool_uses` entry is removed. No existing Lean module is withdrawn.
The other original proof dependencies remain needed by the new helper nodes: constant sheaves,
sheafification, compatibility with underlying sets, and exactness of set sheafification.
The five original public imports stay. Proof imports are the new ring assembly and
constant-section modules; the ring-operation module is public because it now declares the
record used in the original signature.

## Where the brief, the DAG or earlier work was wrong

No error in the original statement or unit route was found. The proof uses uniqueness of left
adjoints instead of the DAG's explicit coproduct implementation of the same constant-sheaf
comparison. During development an arbitrary comparison natural only in commutative-ring maps
was too weak: negation of the underlying set is already a counterexample to operation and
section compatibility for the identity functor. The delivered lemmas therefore take a comparison
natural in all set maps; the original theorem constructs it. The discarded statements are not
part of the delivery.

Edge cases checked: the proof of the set comparison uses no final object of either site; the
singleton sheaf is terminal even on a degenerate site. Constant-section normalization is valid
for the zero ring and arbitrary test sheaves. The remaining operation proof uses product and
terminal isomorphisms, not injectivity of sheafification units or nonemptiness assumptions.

## New nodes

`lem-route-inverse-image-constant-set-comparison`: the proved natural comparison for constant
set sheaves and the construction of its underlying constant-ring comparison.

`lem-route-inverse-image-constant-section-comparison`: the proved normalization on constant
sections, for any comparison natural in all set maps.

`lem-route-inverse-image-constant-ring-operations`: the remaining four pointwise operation
identities for a single constant ring; also records the unchanged extracted `RingInverseImage`.

`lem-route-inverse-image-constant-ring-assembly`: the proved construction and naturality of
the ring-sheaf isomorphism from those operation identities.

Change record: `coord/changes/B3-constant-comparison-ring-record-extraction.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.RouteInverseImageConstantComparison": "9844d52420dac06bd90dd52463b2e2422edb4476", "Sheaf.CategoryTheory.RouteInverseImageConstantRingAssembly": "67b4f869db32c278ef000c73aa70addd89540058", "Sheaf.CategoryTheory.RouteInverseImageConstantRingOperations": "8ff4daa31680627cf8b633b5f76ea69b4fd575bb", "Sheaf.CategoryTheory.RouteInverseImageConstantSectionComparison": "6717d5bf591a4293d82eb10c9fcfeddbdadeb6e2", "Sheaf.CategoryTheory.RouteInverseImageConstantSetComparison": "5971c932478c677a7a651ccf52db93137d2b7ce6"}, "results": {"Sheaf.CategoryTheory.GeometricRingInverseImage": {"hash": "013e1e92d2b68770a032ab049171c2941150d63e", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T10:33:12+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
