## What changed

Implemented `WeilConjectures.CompletedCoefficientPushforward.ordinaryStrictImage_exists`
in `Sheaf.Paper.CompletedCoefficientOrdinaryStrictImage`. All existing public signatures,
definitions, and imports are preserved. The helpers are private and construct the actual
levelwise continuous-site pushforward, its strict-system transitions, the finite coefficient
evaluation comparison, and the completed-module tower comparison. The system functor and
additivity are assembled over arbitrary coefficient rings and sites before specialization;
this prevents kernel checking from repeatedly expanding the concrete coefficient presentation.
Sectionwise commutative squares are likewise checked over arbitrary module sheaves before
specialization. A section-function helper for arbitrary scalar restriction prevents the
kernel from unfolding quotient constant sheaves when checking successor transitions.
All reducibility changes are local to the proof file.

Validation: the complete proof compiled through `lcompile.py` in 35.1 seconds before
removing profiling markers and an unused-section-variable warning. The delivery command
checks the final cleaned file again, including its axioms and the absence of holes.

The quotient-generator equations determine the supplied finite ring isomorphisms uniquely.
This reduces coefficient transport to naturality of constant sheafification. The tower
comparison is assembled from natural level comparisons and checked on successor transitions.
No normalization, cartesianness, or boundedness assumption is imposed. The construction also
works for zero modules, the first coefficient level, empty sites, and identity scheme maps.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CompletedCoefficientPushforward.ordinaryStrictImage_exists`
(node `lem-pur-completed-coefficient-ordinary-strict-image`).
No holes are added, no statements are split off, and no `sorry` remains in the item.

## No longer needed

The proof does not use `lem-pur-coefficient-system-ordinary-images`, represented by
`SheafOfModules.coefficientSystemOrdinaryImage_exists` in
`Sheaf.Paper.CoefficientSystemOrdinaryImages`. Its general inverse-image functor,
level adjunctions, and exactness package are unnecessary for ordinary direct image along
this concrete continuous site functor. The item's `proof_deps` and proof steps are updated
to remove this edge. This is a local dependency pruning; the declaration and its module
remain available to other consumers, including the indirect import through
`CompletedCoefficientPushforwardModels`. No whole module or existing import is removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cited the generic ordinary image package for the first step,
but the concrete continuous-site module pushforward and its Mathlib composition comparisons
suffice and directly supply the required identity on sections. The supplied systemEvaluation
isomorphisms are already natural in systems, so their composite proves this naturality
without separately using systemMap. The mathematical statement and the unit route are kept.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
