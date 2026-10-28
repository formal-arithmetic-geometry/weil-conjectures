## What changed

Proved `WeilConjectures.integralDualizing_mapping_tower_limit_roos_iso` in
`Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitRoos`, preserving its statement.
Added a private proof import of
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
Three proved private helpers transport a Roos triangle through product and object
isomorphisms, invert a comparison square, and identify the canonical Roos triangle
for an arbitrary strict tower. The latter adapts the existing private argument in
`IntegralDualizingRoosModel`, using the actual normalized evaluation functors and
transitions directly. No definition, public declaration signature, or public import changes.

The chosen limit specification provides its auxiliary evaluation, localization
factorization, and triangle. The proof compares the auxiliary and canonical evaluations,
including their successor maps, then transports the triangle between the two product
witnesses. Both resulting limit triangles use the same transition endomorphism.
The existing general noncanonical uniqueness theorem finishes the argument.
The node's proof and proof dependencies now describe these two steps.
Single-file server compilation succeeded in 14.3 seconds before the final scoped
linter annotation. The existing geometric hypotheses are preserved; the unused-section-variable
linter is disabled only for the theorem, since categorical uniqueness does not use them.

## Proved and sorry left

Closed one hole:
`WeilConjectures.integralDualizing_mapping_tower_limit_roos_iso`
(node `lem-coef-integral-dualizing-mapping-tower-limit-roos-iso`).
No holes remain in the item; no holes added and no statements split off.
All three private helpers have complete proofs.

## No longer needed

No imports or modules removed. The theorem `integralDualizing_roos_model` itself
is not a proof dependency: its existentially chosen finite dualizing tower is
unnecessary for this arbitrary-tower uniqueness statement. Its module remains the
public source of the unchanged limit and presentation definitions.
The extra counit isomorphism and compatibility clauses of the presentation are
unused by uniqueness. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old proof step claimed that `integralDualizing_roos_model` supplied the
canonical Roos triangle for the input tower. Its public conclusion supplies a
triangle only for its own existentially chosen tower. The needed arbitrary-tower
argument was private in that module. This proof derives it directly from the
published strict-tower derived-limit specification, without changing the other
module or exposing its helpers.

Searches: LeanFinder returned general derived-category triangle facts, without an
exact project-specific match; Loogle returned no match for `IsDerivedLimit`.
Repository search located the proved `exists_isDerivedLimit_and_iso` and the
existing private evaluation/product transport. The proof uses the former directly
and adapts the latter, with no new mathematical assumptions.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimitRoos": "e6ac7c00301e74104a8816c4dace28393f4987fb"}, "results": {"Sheaf.SixFunctors.IntegralDualizingMappingTowerLimit": {"hash": "5c902229735853a11f6d1fdc929f65f328224583", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T12:03:46+0800", "transitive": 0, "version": 1}
```

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
