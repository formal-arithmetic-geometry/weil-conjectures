## What changed

Proved `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_canonical_exact_structures`
without changing its statement or public imports. The proof constructs normalized tensor
shifts, uses the fixed geometric adjunction with its compatible right-adjoint shifts, and
transports exactness along `sourceIso` and `targetIso`. The existing scalar projection
normalization identifies the restricted scalar mate with the composite of these isomorphisms
and the projection transformation; composition gives its shift compatibility.

Added `Sheaf.Paper.ProEtaleProjectionFirstVariableExact`, with a proved native-universe
projection theorem. Its private helpers prove exactness in the first tensor variable using
the K-flat fixed tensor theorem and resolving descent. They transfer the first-variable
comparison shift square through the canonical pullback isomorphism. The proved abstract
adjunction projection-map theorem then supplies the projection transformation and its shifts.
All added imports are private proof imports except the new module's public data import.
No existing definition, statement, attribute or public import was changed.

Validation: `lcompile.py --all` compiled both delivered modules without warnings,
in 38.2 seconds for the projection module and 26.3 seconds for the assigned module.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_canonical_exact_structures`
(node `lem-sfb-derived-scalar-canonical-exact-structures`).

The new theorem
`AlgebraicGeometry.Scheme.DerivedScalarMate.proEtale_projection_first_variable_exact`
(node `lem-sfb-proetale-projection-first-variable-exact`) and all private helpers are proved.
There are zero holes in the two delivered modules, and zero holes added or split off.
The proof uses existing imported statements, including the unchanged
`scalarMate_projection_normalization`; it does not claim to close their independent holes.

## No longer needed

No original import was removed: the assigned module originally imported only its data module.
No module is withdrawn, and no whole-library module is claimed pruned.

The assigned node's proof no longer directly uses
`lem-weil-pbc-ring-sheaf-change-adjunction`, `lem-pur-derived-change-of-rings`,
`lem-pur-derived-tensor-additive-constraints`, or `def-weil-pbc-proetale-operations`.
It transports the projection functors' exactness and shifts through the already prescribed
scalar comparison isomorphisms instead of repeating these constructions. Those dependencies
can remain necessary to other nodes and to the data/normalization modules.

The direct use of `lem-sfb-ringed-projection-first-shift` is replaced by the new native-universe
projection proof. The older theorem is not withdrawn; its transitive imports remain intact.
The new proof uses its underlying proved K-flat, normalized-comparison and abstract mate tools.

## Where the brief, the DAG or earlier work was wrong

The planned direct specialization of `ringedProjectionFirstShift` does not fit the native
small pro-etale site universes: `RingedTensorCorner` identifies the site object and morphism
universes, whereas the native site has objects in `u+1` and morphisms in `u` with coefficients
in `u+1`. The new theorem gives the needed argument in those original universes. The existing
native mate exactness result varies the coefficient (second tensor argument), while this
item needs the geometric complex (first tensor argument); the proof keeps that distinction.
Neither issue changes or disputes the assigned mathematical statement or the unit route.

## New nodes

`lem-sfb-proetale-projection-first-variable-exact` records the proved first-variable exactness
and shift compatibility of the native projection mate before transport to the scalar mate.
Its module is `Sheaf.Paper.ProEtaleProjectionFirstVariableExact`. The node records the
representative exactness argument, canonical comparison transport, abstract adjunction mate
calculation, sources and searches. There is no change record because no existing interface
or definition was changed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
