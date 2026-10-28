## What changed

Proved `AlgebraicGeometry.Scheme.sfIntrinsicDirectComparisonTransport` in
`lean/Sheaf/Paper/IntrinsicDirectComparisonTransport.lean` without changing its statement,
public definitions, or imports. Three proved private helpers establish the calculation for
arbitrary categories, equivalences, comparison isomorphisms, and a natural transformation.
The public theorem specializes this calculation to the fixed-scalar derived mate.

The proof first expands one transported right comparison and cancels the target equivalence
unit/counit. Naturality of the comparison and the source triangle identity give its normalized
component. Naturality pastes the two comparisons, and naturality of the arbitrary final
transformation moves the last source unit inverse to the required ambient coordinate.
The DAG proof now records these actual steps.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.sfIntrinsicDirectComparisonTransport`
(node `lem-sf-intrinsic-direct-comparison-transport`).
Added 0 holes; split off 0 statements. The delivered module contains 0 `sorry`s.
The three private helpers are proved in full.

Validation: the complete module compiled cleanly through `lcompile.py` in 10.6 seconds.
The delivery tool also runs its declaration/axiom probe and stage-3 preflight.

## No longer needed

The proof does not use `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
(`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`): the comparison transport
works for any natural transformation, so it needs no pushforward-composition theorem.
Removed that node from `proof_deps` and the proof step uses.

`def-sp-finite-intrinsic-pullback` is also unnecessary as a direct proof dependency and was
removed from `proof_deps`. It remains a statement prerequisite; no definition is withdrawn.
The derived-operation definition node `def-weil-pbc-proetale-operations` records the existing
fixed-scalar adjunction specialization used here.

No Lean import was removed: both existing public imports are needed by the unchanged public
statements and definitions. No module or declaration is withdrawn, and no whole-library
module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The current server queue lists this as a proof item with 1 hole; there is no current rework,
return, or build-error entry for it. Despite the long decomposition chain, this particular
comparison-square step is purely formal. The listed derived pushforward-composition theorem
is not needed. The existing statement and ambient-coordinate construction agree, with no
normalization assumption beyond naturality of the comparison isomorphisms.

The generic proof works for any object, without a K-injectivity assumption, and any final
natural transformation; the public theorem keeps its original hypotheses and conclusion.
No new data is chosen and no shared interface is changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntrinsicDirectComparisonTransport": "5e54a1d86ea1b4bf8bfd6b4853e2979dc73ad5f5"}, "results": {"Sheaf.Paper.IntrinsicConjugateComparisonTransport": {"hash": "412c8e1c817834fb7465b50badbf1d1530e178b6", "status": "OK"}, "Sheaf.Paper.IntrinsicDirectCompositorCoordinatesMatePasting": {"hash": "8c9474b340c9aeefcaae9125126369c1ce28a798", "status": "OK"}}, "seconds": 127, "time": "2026-10-28T14:14:32+0800", "transitive": 0, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
