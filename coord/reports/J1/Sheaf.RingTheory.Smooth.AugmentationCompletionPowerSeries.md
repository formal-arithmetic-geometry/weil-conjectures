## What changed

`Algebra.exists_augmented_completion_powerSeries` keeps its statement and now has a
complete proof from two new, strictly simpler lemmas. The proof-only imports are
`Sheaf.RingTheory.Smooth.AugmentationFirstOrderCoordinates`,
`Sheaf.RingTheory.Smooth.AugmentationPolynomialTruncations`, and
`Mathlib.RingTheory.MvPowerSeries.Equiv`.

The assigned module includes proved private helpers for transition compatibility and
passage from finite quotient bijections to completion coordinates. This construction
uses `AdicCompletion.liftAlgHom`, proves both inverse identities by `ext_evalₐ`, and
composes with Mathlib's polynomial-completion/power-series equivalence. The constant
coefficient equation is proved by passing to the degree-one quotient and checking
polynomial evaluation on coefficients and variables. There are no data definitions
chosen from an unproved existence theorem.

## Proved and sorry left

Closed the assigned module's one hole:
`Algebra.exists_augmented_completion_powerSeries`.

Added two named holes in separate modules:

- `Algebra.exists_augmented_firstOrder_polynomial_coordinates`, node
  `lem-sbc-smooth-augmentation-first-order-coordinates`.
- `Algebra.bijective_augmented_polynomial_truncations`, node
  `lem-sbc-formally-smooth-augmentation-truncations`.

This is a decomposition, not a complete mathematical proof. One upper hole is closed
and two lower holes are added (net -1). The inverse-limit construction and augmentation
compatibility are proved, rather than split off. The first remaining lemma uses
smoothness and locality only to produce a finite first-order coordinate map. The
second assumes that first-order map and uses only formal smoothness to propagate it;
it has neither locality nor a coordinate-existence conclusion.

## No longer needed

No original proof imports were removed, and the original node had no proof dependencies.
No existing node or library module is pruned. The inverse-limit step needs no new
unproved module: it is proved locally using Mathlib. All newly added proof imports are
used. The unit's smooth section completion step is retained.

## Where the brief, the DAG or earlier work was wrong

The original node had three non-elementary steps with empty `uses` and no proof
dependencies. No library declaration stated the augmented first-order coordinates or
the finite-order induction in the required generality. The new nodes supply precisely
these missing steps; the remaining completion step is now actual Lean code.

Read Stacks Tag 05D5 at https://stacks.math.columbia.edu/tag/05D5. The local coefficient
ring assumption is needed only for freeness of the finite projective conormal module.
No Noetherian assumption was added. The first-order statement was checked in rank zero
(C = B with identity augmentation), polynomial algebras, and a polynomial algebra times
a smooth component killed by the augmentation. The truncation statement includes k = 0
(both quotients zero), k = 1 (the augmentation quotient), k = 2 (the given bijection),
and empty variable sets. Formal smoothness supplies square-zero lifts in the induction.

Searches are logged in searches.jsonl: LeanSearch was unavailable (HTTP 500), LeanFinder
returned formal-smoothness lifting and completion equivalences but no coordinate theorem,
Loogle returned completion APIs, and grep found cotangent, smoothness, and completion
supporting APIs. Blueprint searches for 05D5, augmentation, and formal smooth polynomial
truncation found no exact existing blueprint statement for either new lemma.

## New nodes

`lem-sbc-smooth-augmentation-first-order-coordinates` states the existence of polynomial
coordinates inducing a bijection only modulo the square of the augmentation ideal.
Its proof follows the conormal basis and split square-zero algebra argument of Tag 05D5.

`lem-sbc-formally-smooth-augmentation-truncations` states the propagation of an already
given first-order polynomial coordinate map to every finite quotient. Its proof follows
the formal smooth lifting and correction of variables in Tag 05D5. Its formal smoothness
hypothesis is explained inline in the node, rather than citing a nonexistent definition
node. Both new Lean theorem docstrings give the full proof for the next worker.

No statement, definition, public import, or existing signature changed. No adaptations
or change records are required. Independent second reading is left to the second worker.

## Second reading by J1

1. I compared `AugmentationCompletionPowerSeries.lean` with the repository version. The
existing theorem signature is byte-for-byte unchanged; only proof imports, private
helpers, and the proof body changed.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile cleanly.
The assigned module has no `sorry`s or hollow definitions and contains no forbidden
declarations. The only remaining holes are the two named split theorems.

3. The split statements are strictly smaller parts of the parent: square-zero
coordinates and propagation to finite truncations. Their Lean statements, docstrings,
and DAG nodes agree, and the documented rank-zero and low-degree cases are included.

4. The proof keeps the unit route through first-order coordinates, finite truncations,
compatible inverse limits, and the power-series completion equivalence. The completion
and constant-coefficient steps are proved in Lean; no original route dependency is
bypassed.

5. The DAG proof steps and `proof_deps` match the theorem calls and imports. The new
nodes contain the required source, proof origin, search, creation, blueprint, and Lean
records.

Independent grep search for `conormal.*free|cotangent.*augmentation|quotient.*formally.*smooth`
found only supporting formal-smoothness lifting API, not either split statement.
I checked Tag 05D5 directly against the two docstring arguments. The dry run compiles
all delivered files and runs the declaration axiom probe successfully; the parent
retains `sorryAx` through the two listed split theorems, and no extra axiom is introduced.

I changed only this report; no Lean proof, statement, definition, or DAG record needed repair.
