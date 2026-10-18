## What changed

Proved six of the seven original theorem holes in
`lean/Sheaf/Paper/LisseAdicFiberFunctors.lean`, with every existing signature,
visibility, definition and public import unchanged. Added the proof-only import
`WeilConjectures.CategoryTheory.Sites.Point.Linear` for scalar linearity of stalk maps.

The rational functor is constructed explicitly: its Hom map is the balanced tensor
extension of integral fibre maps followed by linear base change. Integral additivity
and scalar linearity are checked against every limit projection; identity and
composition follow by tensor induction and the prescribed rational composition law.
The two fixed-model functor laws are obtained by composing the proved fibre inclusion
into the pseudofunctor Grothendieck construction with category transport and localization.
The displayed-model fibre equality cancels inverse category transports. The object
specifications follow from the original existence-witness specifications.

No alternate mathematical route is used: these are the arguments already specified
in the declaration docstrings of `def-pod-lisse-adic-fibre-functors`.

## Proved and sorry left

Closed the original holes in these declarations (all in namespace
`AlgebraicGeometry.Scheme`):

- `lisseRationalFiberFunctor_exists`.
- `lisseRationalFiberFunctor_obj`.
- `lisseAlgebraicModelMap_id`.
- `lisseAlgebraicModelMap_comp`.
- `lisseAlgebraicFiber_ofModel`.
- `lisseAlgebraicFiberFunctor_obj`.

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
(node `def-pod-lisse-adic-fibre-functors`). No holes were added or split off.

The rational existence proof uses the already stated rational composition and category
laws of `LisseAdicSheaves`; those declarations may still depend on sorry. The algebraic
object specification still depends on the remaining algebraic existence theorem.
Thus six direct theorem holes are closed; this does not claim six axiom-free transitive
closures.

## No longer needed

None. The original public import `Sheaf.Paper.LisseAdicSheaves` remains necessary for
the statements and definitions. No original proof-dependency modules or DAG nodes
were bypassed. An experimental explicit import of
`Mathlib.CategoryTheory.Linear.LinearFunctor` was removed because the final proof
requires no additional import of it.

## Where the brief, the DAG or earlier work was wrong

The assigned node has an empty `proof` and `proof_deps`, so there is no numbered DAG
proof to instantiate. The existing declaration docstrings give the proof plan used here.
No statement or definition error was established.

The remaining algebraic existence theorem needs the natural comparison between the
ramified, reindexed integral scalar extension and its inverse-limit geometric fibre,
then rationalization and coherent compatibility with the specified coefficient
pseudofunctor before localization. The finite-level stalk/scalar lemmas do not directly
state this adic comparison. It has not been replaced by a restated lower theorem.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
