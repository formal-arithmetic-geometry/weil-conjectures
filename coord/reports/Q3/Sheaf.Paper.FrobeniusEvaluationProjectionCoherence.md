## What changed

Filled six theorem proofs in `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence`.
All existing declaration signatures, definitions and public imports are unchanged.
Two proved private helpers compute the carrier maps of the curried tensor lift.

`ordinary_projection` uses the right-adjoint projection of the supplied lifted
adjunction and identifies its carrier using the supplied unit, counit and tensor
normalizations. `open_projection` constructs the inverse open projection using
that lifted adjunction's left projection. Its carrier is the specified inverse
gamma; the faithful forgetful functor reflects its invertibility, and cancellation
identifies the carrier of its inverse with gamma itself. `compact_projection`
composes the ordinary projection, the lifted open projection, and the supplied
Weil pullback compositor, then checks the exact prescribed carrier formula.

`OpenSquare.realized_open_square` applies the supplied coefficient representative
function to `OpenSquare.open_square`. `refinement_compatibility` uses faithfulness
of the forgetful functor. `refinement_transport` conjugates by the supplied
refinement isomorphisms and uses the underlying equality to identify its carrier.
Neither proof inverts a projection map.

The proof follows DAG steps 2, 4 and 6 and the inverse-gamma argument already
recorded in the open_projection docstring. The evaluation and normalized system
open-square construction remain the existing named theorem obligations.
The node proof and proof_deps now describe these supplied-domain arguments.
No statement or definition repair, consumer adaptation, or new node is introduced.

## Proved and sorry left

Closed six of the original ten holes (names below are in
`WeilConjectures.PodEvaluationProjection`):

- `ordinary_projection`
- `OpenSquare.realized_open_square`
- `open_projection`
- `compact_projection`
- `refinement_compatibility`
- `refinement_transport`

Added zero holes and split off zero statements. This is a partial proof delivery,
not a decomposition. The four original holes left, all attached to
`lem-pod-frobenius-evaluation-projection-coherence`, are:

- `rational_evaluation`
- `common_evaluation`
- `OpenSquare.transport_exists`
- `OpenSquare.open_square`

Their statements and proof docstrings are unchanged. The realized-square result
uses the existing open_square obligation. The three projection and two refinement
proofs introduce no new unproved mathematical dependencies.

## No longer needed

Removed these unused proof imports from this module:

- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`
- `Sheaf.Paper.FixProjectionCompactificationComparison`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Compactification.BaseChange`

The supplied-domain projection statements already provide the lifted adjunctions,
comparisons and normalization equations. Their proofs need no compactification
existence argument. The refinement statements already supply the underlying
refinement identity, and realization is a function applied to an equality.

No module or DAG node is withdrawn or claimed globally unnecessary: the remaining
open-square proof plan still cites the realization and tensor coherence nodes,
and other modules can still use the geometric compactification theorems. The DAG
plan for those pending obligations and the unit route are retained. The proved
supplied-domain arguments no longer need proof dependencies
`lem-fix-projection-compactification-comparison`,
`lem-pod-semilinear-exchange-cube-coherence`,
`def-weil-derived-pullback-tensor-hom`, `thm-nagata-compactification`,
or `lemma-nagata-compactification-base-change`; these are removed from this
node's proof_deps. Removed top-level tool_uses approvals for
`lem-fix-projection-compactification-comparison` and `thm-nagata-compactification`;
the remaining approvals keep their original order. The underlying refinement
identity and its Weil comparison maps are explicit hypotheses here.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the declarations proved here. The generic supplied
domain interfaces make their categorical proofs shorter than reconstructing the
geometric input data. Existing rational evaluation and transpose lemmas with
structurally separated scheme hypotheses cannot directly discharge this module's
nonseparated model domain; no such hypothesis was added.

One compile could not start because the server temporary directory reported no
space left on device. A later compile resumed normally; no tool was modified.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
