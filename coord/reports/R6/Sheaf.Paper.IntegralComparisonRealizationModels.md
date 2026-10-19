## What changed

Proved four of the five existing theorem holes in
`Sheaf.Paper.IntegralComparisonRealizationModels`, without changing any public
signature, definition, visibility, or normalization predicate. Two private, fully
proved generic helpers isolate the derived-counit normalization and the
limit-to-Roos construction from coefficient-universe instance inference.
Updated the existing node's proof plan to record these arguments and the remaining
system-adjoint obligation. Removed one unused proof import.

## Proved and sorry left

Closed (all attached to `def-trf-integral-comparison-realization-models`):

- `WeilConjectures.integralComparisonTowerCounit_computes`: derived counit
  factorization, cancellation on K-injectives, and localization comparison formulas.
- `WeilConjectures.integralComparisonReductionCounit_formula`: the counit identity
  for uniqueness of left adjoints and the composite-adjunction counit formula.
- `WeilConjectures.integralComparisonLimitToRoos_existsUnique`: explicit limit-tuple
  map killed by 1-s, lifted with zero second coordinate; uniqueness in each degree
  follows from the mapping cocone's two-coordinate identity.
- `WeilConjectures.integralComparisonRestrictedSectionType`: the restriction
  functor's chosen specification followed by the evaluation section equation.

One original hole remains:
`WeilConjectures.integralComparisonSystemRestriction_isRightAdjoint`
(node `def-trf-integral-comparison-realization-models`). It still needs the
constant-ring sequence-site equivalence, identification of the actual restriction
functor, and the derived tensor/restriction adjunction. No new holes or split-off
modules were added. Counts: five original holes, four closed, zero added, one left.
Proofs may still depend on the library's existing theorem holes, as intended by
stage 3. In particular, the counit formula uses the original system-adjoint hole.

## No longer needed

Removed the proof import
`Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`. None of its declarations
is used by the four proofs or by this module's interface. No public imports were
removed. The existing node had no proof-dependency list to prune. No new mathematical
lemmas or nodes are required: Mathlib's derived-adjunction factorization,
adjoint-uniqueness API and mapping-cocone constructors provide the categorical glue.
No whole module is claimed globally unreachable; the removed import edge is the
pruning in this delivery.

## Where the brief, the DAG or earlier work was wrong

The retained earlier attempt's `rfl` for restricted section types did not compile
against the current published library: coefficientSequenceRestriction is chosen
from its uniqueness theorem. The proof now uses its specification explicitly.
The existing DAG node is a definition node with an empty proof plan, even though
its module contains five theorem holes. Its proof field now records the actual
arguments and identifies the original theorem that remains open. No mathematical
statement is disputed or changed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
