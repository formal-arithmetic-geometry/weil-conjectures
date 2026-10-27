## What changed

Replaced the proof of `AlgebraicGeometry.field_extension_component_local_dimension`.
Added the proof-only import `Sheaf.AlgebraicGeometry.LocallyAlgebraicDimensionComponents`.
All existing signatures, definitions, public imports and docstrings are unchanged.

Two proved private helpers transport local dimension along a homeomorphism and identify
local dimension in a fibre over the spectrum of a field with local dimension in the source.
The latter constructs the homeomorphism using the existing fibre embedding and its
surjectivity, since the field spectrum is a singleton. Fibre-dimension base change then
gives the pointwise equality. Local Noetherianity follows from base change of local finite
type and Mathlib's locally-Noetherian-source theorem. Sobriety supplies generic points.
At such a point, closedness and maximality identify the component furnished by the declared
maximum formula with the given component. The constant-dimension consequence is substitution.
This follows the existing DAG route, so no node changes are necessary.

Validation: the complete module compiled through `lcompile.py` with exit code 0,
no warnings, in 3.3 seconds. The import-direction check confirmed no import cycle.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.field_extension_component_local_dimension`
(node `lem-trf-field-extension-component-local-dimension`).
Added 0 holes; no `sorry` remains in the delivered module.

The proof uses the existing declaration
`AlgebraicGeometry.topologicalKrullDimAt_eq_max_component_dimension`
(node `lem-trf-locally-algebraic-dimension-components`), whose proof remains `sorry`
in its unchanged dependency module. This is a proof from the project's stated dependencies,
not a claim that all transitive dependencies have been proved.

## No longer needed

None. No imports or declared dependency nodes were removed. The proof follows all five
steps of the existing node and keeps the unit route. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The fibre-to-whole-space identification needed elementary Lean glue: it is a
homeomorphism of topological spaces, sufficient for local topological dimension, with no
need to construct a scheme isomorphism or choose an unproved existence witness.
The proof works for empty schemes without a nonemptiness hypothesis, and for arbitrary
field extensions without algebraicity or separability hypotheses.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
