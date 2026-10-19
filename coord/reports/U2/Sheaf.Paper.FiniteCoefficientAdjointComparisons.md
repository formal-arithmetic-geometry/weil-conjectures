## What changed

Replaced seven helper proof holes in `Sheaf.Paper.FiniteCoefficientAdjointComparisons`.
`stageFinite` uses injectivity of the field inclusion to show the defining ideal is nonzero,
then the target DVR classifies it as a power of its uniformizer ideal. Finiteness follows
from the finite residue quotient and `Ideal.finite_quotient_pow`. This handles ramified
stages without equating the base and target uniformizers.
`Arrow.ideal_le` transports the parameter using `over_base` and reverses the exponent
inequality for ideal powers. `Arrow.ringMap_id` and `Arrow.ringMap_comp` are proved on
quotient representatives, comparing integer maps through their injective field inclusions.
`etaleLeftAdjoint` applies the existing upstream ambient-adjoint theorem for the specified
compactification. The two geometric helpers use Mathlib's finite-type and quasi-compact
Noetherian criteria and cancellation of morphism properties over the base.
Added the proof-only import `Mathlib.RingTheory.Ideal.Quotient.Index`.
No statement, definition, visibility, or target signature changed.
Current-source validation: `lcompile.py` compiled the complete module in 13.3 seconds,
exit code 0, without errors or warnings. A direct-source `#print axioms` audit compiled
in 13.7 seconds and confirms the dependency accounting below. The module has one
remaining source `sorry`, and all lines have at most 100 characters. The sandbox
retains the seven original public imports and every current planned proof import.
The seven theorem signatures and all existing definitions are unchanged.

## Proved and sorry left

Closed seven of the original eight declaration holes, all in namespace
`AlgebraicGeometry.FiniteCoefficientAdjoints`:

- `stageFinite`.
- `Arrow.ideal_le`.
- `etaleLeftAdjoint`.
- `Arrow.ringMap_id`.
- `Arrow.ringMap_comp`.
- `finiteTypeNoetherian`.
- `finiteTypeMorphismProperties`.

The sole remaining hole is
`AlgebraicGeometry.FiniteCoefficientAdjoints.finite_coefficient_adjoint_comparisons`,
node `lem-pur-finite-coefficient-adjoint-comparisons`. Its existing signature and complete
15-step proof docstring are unchanged. No holes were added or split off. The remaining
work is the construction of the normalized adjunction/coefficient/refinement system,
using the stated ordinary-etale support and comparison results, together with the
finite-free and ramification conclusions. The helper proofs do not claim that all their
imported dependencies are themselves free of `sorry`. The sandbox axiom audit shows
that `etaleLeftAdjoint`, `finiteTypeNoetherian`, and `finiteTypeMorphismProperties` use only
`propext`, `Classical.choice`, and `Quot.sound`. The four coefficient-algebra helpers still
transitively depend on `sorryAx` through the recorded coefficient/integer-map dependencies;
their own proof holes are closed. The temporary audit module was removed.

## No longer needed

None. The main theorem and its planned dependencies remain open; none of its nodes or
modules is claimed pruned. The helper proofs use shorter existing APIs within Steps 1,
5, and 14, without changing or bypassing the unit route. No imports were removed.

## Where the brief, the DAG or earlier work was wrong

The ambient adjoint bridge requires no fresh Noetherian proof for the compactification:
`Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification` already applies to any
compactification and finite commutative coefficient ring. The recorded Noetherian
hypotheses of the bridge remain unchanged. The other helper plans are valid.

The earlier session's required delivery dry run failed in launcher worktree creation:
its detached checkout timed out before preflight, and its queued retry was interrupted.
The resumed session retained those proofs and checked them against the current source.
A new dry run was interrupted while waiting for worktree capacity; after confirming
that no delivery process remained, the retry reached the delivery preflight. These
were delivery infrastructure delays, not Lean compilation failures. No launcher
script or lock was changed. The final delivery command records the authoritative
preflight and push outcome.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
