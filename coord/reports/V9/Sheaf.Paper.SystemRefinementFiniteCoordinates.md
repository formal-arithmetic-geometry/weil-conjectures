## What changed

The assigned statement and its public imports are preserved. Its proof now has a real
assembly of the identity-normalized proper/open factor and the direct-image compositor
at one finite evaluation. The finite-operation normalization half is proved by reusing
the argument already present in FiniteRefinementProjectionRealization: choose a bounded
constructible etale origin, reverse finiteRefinementNormalization, identify the witness
arrow with refinementComparisonAtWitness_inv_eq, and transport by naturality. That
module's needed helpers are reproduced privately because its support_refinement lemma
is private; its tensor/projection theorem is not imported. The small supportRealization
composite is also private here, avoiding an import of ConstructibleProjectionMates.

SystemFiniteEvaluationCoordinates constructs all coordinate isomorphisms explicitly
from the given evaluations, coefficient counits, normalized direct/open comparison and
coefficient inverse units. It proves direct-coordinate naturality and the support
pasting formula. Two new modules isolate the proper/open-factor evaluation and the
direct-compositor evaluation. The item pastes their fixed-coordinate squares and
transports along e, then cancels the support isomorphisms. The categorical pasting,
coefficient realization and final cancellation are proved in generic private helpers;
local irreducibility prevents expensive unfolding of the system and finite comparisons. No existing dependency file,
definition, instance, statement, attribute or public import is changed.

## Proved and sorry left

Closed the item's one hole in
WeilConjectures.FixProjectionCompactification.systemRefinementFiniteCoordinates.
There are zero remaining holes in the item and zero in the coordinate constructions.
All four packet modules compiled on the project server. The final item compile
was clean (no errors or warnings) and took 41.2 seconds; profiling options are removed.

Added two holes, so this is a decomposition (one upper hole closed, two strictly
smaller operation-level holes added), not a net proof:

- WeilConjectures.IntegralSystemRealization.FiniteCoordinates.compositor,
  node lem-sf-system-finite-compositor-coordinates.
- WeilConjectures.IntegralSystemRealization.FiniteCoordinates.refinementMate,
  node lem-sf-system-finite-refinement-mate-coordinates.

The compositor lemma has arbitrary composable scheme maps and inputs, with no open
operation, support functor, constructibility, or finite-operation datum. The mate lemma
omits the outer proper image and its compositor, the finite-operation datum and its
normalization, and the input identification e. Neither restates the assigned equation.
Their sources, complete proofs in words, and edge cases are recorded in their own
modules and nodes. The top-level proof performs both pasting and finite normalization.

## No longer needed

No original public import is removed. The existing semilinear mate and canonical-bridge
nodes are used by the new proper/open-factor obligation rather than directly by the
item; they remain needed transitively. The finite origin theorem remains needed in the
item's private normalization proof. No declared dependency is claimed globally pruned.

The proof does not use the tensor or projection parts of
FiniteRefinementProjectionRealization or ConstructibleProjectionMates; neither module
is imported. No node, module, unit step or upstream declaration
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The current item has its source in lean/ despite the historical quarantine row, and
has one hole. The claimed source and its statement are retained. The DAG's single
finite-evaluation step concealed two distinct normalized operation comparisons, neither
already exposed for the o evaluations in the library. Those are now stated separately;
the intervening coefficient-equivalence cancellations and the final finite-operation
normalization are actual proofs, rather than another renamed copy of the whole item.

The project-specific normalization cannot be supplied by generic Mathlib mate lemmas
alone: those lemmas do not identify the prescribed derived representatives and section
normalizations. Existing finite witness normalization is already proved and is reused.
The unit has no realized steps, and the current blueprint's compactification-independence
argument is preserved.

## New nodes

- def-sf-system-finite-evaluation-coordinates records the explicit coordinate
  constructions, naturality and support pasting API. All its declarations are proved
  or explicit isomorphism composites; there is no data selected from a holed theorem.
- lem-sf-system-finite-compositor-coordinates records the normalized single-evaluation
  direct-image compositor square, sourced from the compositor factor of the original
  finite-evaluation step and Stacks 03D8/07A7.
- lem-sf-system-finite-refinement-mate-coordinates records just the identity and
  proper/open factors at a single quotient, sourced from that part of the original
  finite-evaluation step and Stacks 03DI/07A7/0F7B.

LeanSearch, LeanFinder/Loogle, Mathlib grep, project-source searches and a blueprint
search found generic mate algebra and the existing normalization ingredients, but no
existing statement of either full new operation-level square. The existing
systemPullbackCompositorEvaluation supplies the inverse-image part of the new
direct-compositor obligation, and its node is recorded as a proof dependency. This
node from the smooth-purity unit is a tool for evaluating the same specified
Compositors.pullComp; no statement in the current unit separately gives that
operation-level equation. No maintainer tool approval field is changed.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
