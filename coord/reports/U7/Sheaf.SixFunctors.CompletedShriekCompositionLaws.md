## What changed

Reduced `WeilConjectures.IntegralSystemRealization.completedShriekIntegralBounds` in
`Sheaf.SixFunctors.CompletedShriekCompositionLaws` to three one-operation bounds
statements. Added private proof imports of `ConstructibleReductionGood`,
`ProperSupportStepBounds`, and `OpenSupportStepBounds`. The proof is induction on the
expression: variables use constructible reduction; proper and open nodes use their
one-operation bounds; compact support applies open bounds then proper bounds. Pullback
and tensor nodes contradict `compactSupportOnly`. A proved private helper extracts the
root geometry needed to instantiate each operation. The domain includes all input
variables, including unused ones, and these are handled separately before induction.

The original theorem signature, definitions, public imports, and all seven proofs
already present in the current shared source are preserved. Updated the parent node's
bounds proof steps and their dependency list. Added three statement modules and their
nodes, with sources and complete proof plans. No source-library module was changed.

All four sandbox modules compile through the remote compiler. The final induction
uses every new private import. The statements were checked against zero objects,
empty schemes and opens, identity opens, unused input variables, and absence of
structural separatedness assumptions. In particular, the proper and open statements
allow unrelated system and integral inputs; their conclusions are independent.

## Proved and sorry left

Baseline: nine holes in the current shared item, after the seven previously landed
proofs. Closed the body of `completedShriekIntegralBounds`, by a complete induction
from three new statements. This is a decomposition: one original hole closed, three
holes added, net two additional holes; it is not a completed proof of the bounds theory.
The private helper `completedShriekGeometricRoot` is proved without holes.

Eight original holes remain, all in namespace
`WeilConjectures.IntegralSystemRealization`, node
`lem-sf-completed-shriek-composition-laws`:

- `completedShriekRefinementLaws`
- `completedShriekTowerRefinement`
- `completedShriekAssociativity`
- `completedShriekUnits`
- `completedShriekChoiceIndependence`
- `completedShriekFiniteEvaluation`
- `completedShriekIntegralComposition`
- `completedShriekSpecifiedIntegral`

Three new holes, each the entire proof of a named theorem in its own module, in the
same namespace:

- `constructibleReduction_good`: `lem-sf-constructible-reduction-good`;
  `Sheaf.SixFunctors.ConstructibleReductionGood`.
- `properSupportStep_bounds`: `lem-sf-proper-support-step-bounds`;
  `Sheaf.SixFunctors.ProperSupportStepBounds`.
- `openSupportStep_bounds`: `lem-sf-open-support-step-bounds`;
  `Sheaf.SixFunctors.OpenSupportStepBounds`.

Actual delivery hole count: eight in the item and three in the new modules, eleven
in total. No holes inside definitions or private helpers were introduced.

## No longer needed

None. No imports, modules, or nodes were withdrawn. The old bounds ingredients are
assigned to the three new nodes rather than asserted to be globally unnecessary.
The unit's route and its own statement remain intact.

## Where the brief, the DAG or earlier work was wrong

The initial source read had sixteen holes; the current shared source had meanwhile
received seven proofs. This packet was based on that updated source and preserves
those proofs. The baseline for this delivery is therefore nine holes.

The bounds argument requires bounds for every input, even an unused input whose
scheme is not covered by the root geometric hypothesis. The reduction statement is
accordingly stated for any scheme over the finite-field base. Proper and open steps
need finite type only on their own source and target, extracted from the geometric
expression. The compactification ambient is finite type via its proper map to the
target; no separatedness hypothesis on the structure maps is added.

No statement is disputed and no existing declaration or definition was repaired.

## New nodes

`lem-sf-constructible-reduction-good` isolates the variable/base case of the common
bounds argument: normalized reductions of a constructible integral object have
uniform cohomology and Tor bounds and compatible origins. It is strictly smaller than
closure under arbitrary compact-support expressions.

`lem-sf-proper-support-step-bounds` isolates a single proper operation, for an already
Good system and an integral constructible input. Its proof plan gives the finite
cover and relative dimension bound, quotient normalization, origin transport, and
integral completeness needed for that one operation.

`lem-sf-open-support-step-bounds` isolates a single quasi-compact open operation.
Its proof plan uses exact extension by zero, the tensor comparison, actual quotient
transitions, origin transport, and completed integral extension. The induction
combines this lemma with the proper lemma at every compactification node.

There are no change records because no existing signature or definition changed.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
