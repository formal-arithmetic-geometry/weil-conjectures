## What changed

Proved the affine tower coefficient comparison by induction on the ordered tower length.
The induction keeps the target descent on the left, applies naturality of one-coordinate
coefficient descent, then cancels the final descent isomorphism. The zero case uses the
canonical derived inverse-image identity laws. The successor combines the preceding
coefficient square with the proved normalized shifted-line square by tensor naturality
and monoidality, and pastes the two projection squares.

Added a single-coordinate descent base-change theorem in its own module. Its proof
expands the projective-line comparison, transports it through the affine chart tensor
comparison, pastes the chart and projection squares, and applies shifted-line square
coherence on both squares. This is a proved helper, not a new postponed obligation.
All generic formal-calculus helpers are private and proved. Only the assigned module,
its node, and the new helper module/node are changed. No shared interface or target is changed.

Both modules compiled individually through the server compiler, with no holes in either.
The complete core proof compiled in about 26 seconds. Local transparency attributes avoid
unfolding large derived functors during proof checking; they change no exported interface.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.Etale.affineTraceRightBaseChange_unit_coefficient`.

Added zero holes. The new theorem
`AlgebraicGeometry.Etale.affineLinearLineDescent_baseChange` is proved.
There are no `sorry` declarations in either delivered module.

## No longer needed

The proof does not use `lem-amb-ordinary-finite-unit-pullback-comp` or import
`Sheaf.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp`: length zero follows from
the canonical inverse-image identity laws for an arbitrary input isomorphism.
This is pruning of the assigned proof's dependency, not withdrawal of the declaration.

The statement module `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`
is also not imported: the proof uses its already proved source-library component APIs
for tensor-square monoidality, naturality, and composition associativity directly.
Its wrapper node `lem-kun-derived-pullback-composition-monoidal` is removed from the
proof dependencies: the component identities already have proved source declarations. Neither original public import is removed.
No existing module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The old one-step plan omitted the compatibility of the affine-chart restriction and
single-coordinate descent with right base change. That calculation is now made explicit
in the new proved helper and recorded in the DAG. The old zero-case instruction to use
constant-unit pullback composition was unnecessary; identity coherence suffices.
No false statement, hollow definition, or signature repair was found.

Edge cases are preserved: tower length zero is proved separately, arbitrary input
objects and isomorphisms are allowed in the one-coordinate lemma, and normalized
shifted-line coherence already covers N = 0 and empty schemes. No finite-coefficient,
positive-rank, positive-N, or nonempty-scheme hypothesis is added.

## New nodes

`lem-amb-affine-linear-line-descent-base-change`, realized by
`Sheaf.AlgebraicGeometry.AffineLinearLineDescentBaseChange`, is the proved naturality
square for a single affine coordinate. It is strictly the successor ingredient, with
no tower recursion or unit specialization. Its node includes the source, full proof,
Mathlib searches, edge-case scope, and exact Lean signature.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
