## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation_postprefix`
in `Sheaf.Paper.RationalP1SectionEvaluation` by local morphism cancellation.
Proof irrelevance removes the intervening object-equality loop; the forward and
inverse components of the canonical functor comparison then cancel. Functoriality,
tensor functoriality and associativity finish the equality.

Updated the postprefix node to record this elementary proof without geometric
proof dependencies, and the core node to record its actual use of the existing
prefix and postprefix lemmas. No existing signature, definition, instance, attribute,
or import is changed. Added the cancellation docstring and expanded the
remaining prefix's source proof explanation.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation_postprefix`
(node `lem-sfb-rational-p1-section-evaluation-postprefix`).

The one remaining hole is
`AlgebraicGeometry.ProEtale.RationalP1.first_section_tensor_evaluation_prefix`
(node `lem-sfb-rational-p1-section-evaluation-prefix`). Its statement and hole
are unchanged; its proof explanation is expanded. The core
and terminal evaluation retain their existing complete proofs from this prefix
and the now-proved cancellation. No holes are added; no statements are split off.

The cancellation argument is uniform in all objects and arrows, including zero
kernels and zero functionals. It does not use the prefix, projection invertibility,
trace identities, or geometric hypotheses.

## No longer needed

The postprefix proof does not need
`lem-sfb-rational-p1-section-evaluation-prefix`; its old proof dependency was
unnecessary. The core now cites the two lemmas it actually combines instead of
directly citing ringed projection coherence and module/ringed comparison.
Those geometric dependencies are still retained by the unfinished prefix.
No import or module is pruned globally.

## Where the brief, the DAG or earlier work was wrong

The postprefix node formerly described a geometric path/naturality argument and
cited the prefix, although this equality is just cancellation of the canonical
functor-equality transport. The core node did not record the existing prefix and
postprefix decomposition that its Lean proof already used. Both proof records
are corrected; their statements stay identical.

The stale global-build error records missing ambient-composites and Tate-pullback
imports. The current ambient-composites source compiles, and the item resolves
both imports in the present published compile environment.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SectionEvaluation": "568bd60e4bd17738cb3b6ab93b40928594b6e61d"}, "results": {}, "time": "2026-10-28T10:25:59+0800", "transitive": 0, "version": 1}
```

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
