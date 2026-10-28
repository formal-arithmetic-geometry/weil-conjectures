## What changed

Repaired CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq to construct
compatible source and target isomorphisms to the canonical finite quotient model, then
prove their equation. The original arbitrary-isomorphism assertion was false. The proof
uses the existing normalized ordinary finite pull comparison, its proved scalar helpers,
the finite coefficient comparison and the prescribed ordinaryPullComparison insertion
equation. Two scalar-extension adjunctions make comparison on double insertion faithful.

Adapted the unclaimed ConstantCompletionOrdinaryReducedPullTransport caller without
changing its statement or visibility. Updated the item's node, the caller's proof route,
and the existing finite-pull-existence node's stale upward ownership dependency. The
last change prevents a DAG cycle; its Lean theorem and proof remain unchanged.

Change record: coord/changes/F2-ordinary-reduced-pull-normalized-transports.md.

## Proved and sorry left

The repaired theorem CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq
has a complete proof. The original false universal assertion is replaced, not proved;
this is a statement repair, not evidence that the old assertion was true. The unchanged
parent CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport is proved from
the compatible pair. The item had one textual sorry and now has zero. No sorry is added,
no statement is split off, and no sorry remains in any delivered Lean module. All private
helpers are fully proved. Existing unproved dependencies outside this delivery remain
as in the published library.

Validation: the item and caller compile separately in about 30 s and 5 s, with the
delivered item supplying the caller's dependency. All debug/profiler options are
removed. Final delivery runs the axiom probe, preflight and related-importer checks.

## No longer needed

Removed the public import of
Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso from the item. Its four-module
transport-helper chain is no longer needed on this route:

- Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso
  (lem-weil-pbc-constant-completion-ordinary-reduced-pull-source-iso).
- Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso
  (lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-iso).
- Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionIso
  (lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-iso).
- Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetProjectionModelIso
  (lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-projection-model-iso).

These modules and their declarations are retained untouched. The caller's DAG no longer
requires the separate source/target existence nodes; the repaired equation constructs
both at once. The item's old dependency
lem-weil-pbc-common-quotient-ordinary-insertion is also unnecessary for this proof:
the insertion equation is proved directly through the two scalar adjunctions. This
is local pruning; that generic node may still be needed elsewhere. No unit statement
or unit proof step is bypassed. The normalized scalar constructions avoid another
split of the same transport obligation.

## Where the brief, the DAG or earlier work was wrong

The old theorem's quantifiers lost the word "normalized": arbitrary independent
isomorphisms cannot satisfy the equation. The terminal-site, identity-pullback example
with A = F₃ and I = 0 exhibits the nontrivial -1 automorphism. The repair asserts
existence of compatible normalized transports and retains the parent conclusion
verbatim, rather than adding a compatibility hypothesis that assumes the desired result.
Its statement_change lists the sole existing citer,
lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport, as preserved.

The finite-pull-existence node's old dependency on its own parent completion-equivalence
was an ownership reference; its proved ordinary argument does not use that theorem.
The metadata now names only the actual coefficient/inverse-image data, tensor adjunctions
and normalized module adjunction, preserving its Lean theorem and every existing use.
The statement_change records every existing citer. This prevents a cycle when the
transport equation cites the proved finite-pull-existence result.

Edge cases: all constructions use module-sheaf adjunctions, not cancellation of a
coefficient element, surjectivity on global sections, or a nonzero-ring assumption.
They apply to I = 0, I = A, the zero ring and n = 0. The inverse-image adjunction and
finite-limit preservation required for the normalized module comparison are supplied
by the unchanged parent. No target or definition meaning changes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport": "45a140df13283bef31b1b6ddf2b70d31b7586092", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation": "b45d471d3669b846e0d2e7e6c9bf0e549df25f02"}, "results": {}, "time": "2026-10-28T10:23:23+0800", "transitive": 0, "version": 1}
```

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
