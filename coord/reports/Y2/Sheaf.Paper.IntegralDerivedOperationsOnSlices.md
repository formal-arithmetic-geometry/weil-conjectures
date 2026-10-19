## What changed

Proved `WeilConjectures.IntegralOnSlice.roosUnit_condition` by product extensionality:
naturality of the existing augmentation makes its composite with `1-s` zero, and
both zero-cochain contributions vanish. The argument works on the global site and
on every slice and changes no statement or definition.

Constructed the augmentation from the sectionwise extension/restriction scalar
adjunction unit, the module sheafification unit, and the specified object transports
of `reductionWitness`. Private helpers prove its generator formula and naturality.
The successive-transition equation is the existing `transition_existsUnique`
generator formula evaluated at one; assembling it with `NatTrans.ofOpSequence`
gives `augmentation_existsUnique`, with uniqueness checked on all sections.

No imports were added or removed. Both arguments follow the original docstring plans.

Validation: the final module compiled through `lcompile.py` with exit code 0
and no warnings (20.0 seconds), rechecked against the current server dependencies.

## Proved and sorry left

Closed two of the six original holes:

- `WeilConjectures.IntegralOnSlice.augmentation_existsUnique`.
- `WeilConjectures.IntegralOnSlice.roosUnit_condition`.

Four original holes remain, all attached to
`def-pur-integral-derived-operations`:

- `WeilConjectures.IntegralOnSlice.transition_existsUnique`.
- `WeilConjectures.IntegralOnSlice.completion_exists`.
- `WeilConjectures.IntegralOnSlice.completionUnit_existsUnique`.
- `WeilConjectures.IntegralOnSlice.completedTensor_global_comparison`.

No holes were added or split off. The augmentation proof uses the existing transition
hole; the Roos condition uses that augmentation. These close local proof obligations,
not the entire dependency chain.

## No longer needed

None. The existing public imports continue to supply the module's statements and
constructions; no declared DAG dependency or unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item's node is a definition node with no numbered proof steps. Its six supporting
proof obligations and their natural-language arguments are already named in the Lean
module and attached to that same node. This delivery completes two of those arguments
without changing the node's route or introducing statements.

The retained proofs were checked against the current sources and compiled successfully.
The delivery dry run waited for shared worktree capacity; this did not require code changes.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
