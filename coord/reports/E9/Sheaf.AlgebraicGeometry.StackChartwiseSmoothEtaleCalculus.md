## What changed

Partial stage-3 proof delivery for
`Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`.
Four of the eight original theorem holes are filled, without new holes or public
signature changes. Only the item module and its own theorem node are changed.

`stack_chartwise_smooth_etale_calculus` reuses every original space-test witness
through an explicitly constructed equivalence
`T ×_G F → T ×_H (H ×_G F)`. The private insertion functor is proved fully
faithful and essentially surjective, and preserves the projection to T strictly.
This works for an arbitrary scheme property, so the original five-property and
stack hypotheses need no additional assumptions.

`stack_chartwise_implications` keeps the same space witnesses and applies the
Mathlib scheme instances on each chart. A proved private monotonicity lemma
handles the other three scheme-property implications.

`surjective_moduli_baseChange` lifts the image of a field object and constructs
the resulting object of the actual 2-fibre product using `moduliTwoFiberLift`.
`surjective_moduli_comp` lifts successively through the two maps, pastes the
actual comparison isomorphisms and compares successive restrictions with the
restriction along the composite field extension.

The node's steps 1, 4, 7 and 9 describe these shorter routes. The other clauses
retain their existing proof plans. No new modules, nodes or change records.

## Proved and sorry left

Original holes: 8. Holes closed: 4. Holes added: 0. Split off: 0.

Closed, all attached to `lem-sfb-stack-chartwise-smooth-etale-calculus`:

- `CategoryTheory.stack_chartwise_smooth_etale_calculus`
- `CategoryTheory.stack_chartwise_implications`
- `CategoryTheory.surjective_moduli_baseChange`
- `CategoryTheory.surjective_moduli_comp`

The following four original named theorem holes remain unchanged, with their
original complete proof docstrings and the same node attachment:

- `CategoryTheory.stack_chartwise_comp`
- `CategoryTheory.stack_chartwise_openCover`
- `CategoryTheory.surjective_moduli_iff_chartwise`
- `CategoryTheory.etale_moduli_scheme_coproduct`

All private helpers are fully proved. Neither definition in the item changed.

Validation: the complete edited module compiled through `lcompile.py` in
13.2 seconds with profiling enabled. The delivery validation checks the final
version after removing the profiler and debug messages. An earlier attempt
that made Lean infer equalities across fully expanded restriction functors
exceeded the compile limit. Proved private whiskering/pasting helpers and
explicit equalities between discrete-moduli maps fixed that elaboration cost;
no shared definition or time limit was changed.

## No longer needed

Removed the following unused proof imports:

- `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`

The completed proofs require no locality or presentation-criterion theorem:
the base-change test has the same scheme target and projection after formal
reassociation, and each implication uses the same chart witnesses.

`lem-weil-pbc-etale-smooth-zero-dimensional-fibres` is removed from step 9,
`proof_deps` and the item's `tool_uses`: Mathlib already supplies Etale→Smooth,
and this item's implication does not ask for a fibre-dimension conclusion.

The direct base-change argument also removes these now-unused direct proof
dependencies from step 1 and `proof_deps`:

- `lem-pc-proper-base-change`
- `lem-weil-pbc-flat-morphism-base-change`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-weil-pbc-lft-base-change`

Step 1 keeps the scheme composition laws and étale base change needed for
chart operations in the unproved clauses.

The locality, presentation and space fibre-product nodes remain in the DAG
plans of the four unproved clauses. Those nodes are not claimed globally
unnecessary, and no module is withdrawn. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

There is no disputed statement or interface repair. The earlier base-change
plan used stronger geometric machinery than its actual scheme-test encoding
requires. In particular, its first scheme base-change input was labelled
`lem-pc-proper-base-change`, whose current Lean match concerns properness,
not smoothness; the new proof uses neither that input nor any scheme
base-change law for P. Its old space-base-change calculation is replaced by the explicit
insertion equivalence. The earlier implication proof unnecessarily depended on
a theorem also asserting zero-dimensional fibres.

The first search results used newer Mathlib names (`IsEtale`, `IsSmooth`);
the local pinned source has `Etale` and `Smooth`, which are the unchanged
predicates used throughout this delivery.

Edge cases checked in the arguments: empty scheme tests reuse the same space
witnesses; the field-lifting proofs impose no source nonemptiness, and empty
targets have no field test requiring a lift. The reassociation proof works
with arbitrary categories over the base and arbitrary P; it assumes neither
an étale stack atlas nor a finiteness condition.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
