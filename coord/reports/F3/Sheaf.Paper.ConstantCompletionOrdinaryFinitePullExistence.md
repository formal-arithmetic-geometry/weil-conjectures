## What changed

Proved `CategoryTheory.ConstantCompletion.ordinaryFinitePull_exists` with its original
statement. Four proved private helpers compose normalization equations, establish insertion
naturality, compare successive scalar extensions, and compare inverse image with scalar
extension. The public comparison is their composite along the constant-ring naturality
square. Updated the item's DAG proof to describe this route.

The proof reuses the existing fully proved
`WeilConjectures.SemilinearSections.normalizedModuleAdjunction_exists` and the ordinary-pull
restriction comparison APIs, together with Mathlib's adjunction mate and uniqueness APIs.
No public signatures, definitions, instances, or attributes change.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ConstantCompletion.ordinaryFinitePull_exists`.
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
All private helpers have complete proofs. No new modules or nodes are delivered.

## No longer needed

Removed the proof import `Sheaf.Paper.ConstantCompletionDerivedPull`: this ordinary
comparison uses no derived-pullback construction. This does not assert that the module is
unused elsewhere, and no node or module is withdrawn. The original constant-completion
dependency remains needed for the scalar-extension and inverse-image APIs. The unit route
is unchanged. The general normalized module adjunction is already proved, so no new
adjunction construction or tensor-pairing dependency is needed here.

## Where the brief, the DAG or earlier work was wrong

The old single proof step did not specify the invertibility argument or its normalization.
The implemented proof makes both explicit using mates of adjunctions. The theorem's
statement needs no correction. The normalized module adjunction comes from
`lem-coef-normalized-module-adjunction`, a proved library theorem, specialized to the
small sites here; this does not replace any step of the proper-base-change unit.

Profiling showed repeated unfolding of concrete scalar adjunctions and the restriction
comparison during kernel checking. The proof binds these through proved existence
statements with explicit unit and underlying-map equations.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryFinitePullExistence": "6cd1badc783c3dfd37a016fa2f17dd784e977f77"}, "results": {"Sheaf.Paper.ConstantCompletionOrdinaryFinitePull": {"hash": "1511cf7191ee512b808f4ce277ad3a94901698a9", "status": "OK"}, "Sheaf.Paper.ConstantCompletionOrdinaryFinitePullUniqueness": {"hash": "37afb385c26fc9d9cef069c7f0a9605d50e04030", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T04:33:54+0800", "transitive": 0, "version": 1}
```

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
