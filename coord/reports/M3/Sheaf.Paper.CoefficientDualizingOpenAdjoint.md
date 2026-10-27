## What changed

Replaced the item hole by the geometric instance assembly and proofs of both
specified composite-counit equations using right-adjoint uniqueness. Split step 5,
the bounded-below compatibility of the actual normalized compositor, into
`Sheaf.Paper.CoefficientDualizingOpenCompositorPlus`, with its node and proof in words.
The item applies that clause at both finite coefficient levels. All existing public
signatures and definition bodies are unchanged. The four comparison definitions moved
verbatim to the new module, publicly imported by the item, to share their named types
without expanding the concrete constructions in theorem applications. See
`coord/changes/coef-dualizing-open-comparison-location.md`.

## Proved and sorry left

Closed the existing item hole `AlgebraicGeometry.Etale.coefDualizingOpenAdjoint`
(node `lem-coef-dualizing-open-adjoint`). Added one hole:
`AlgebraicGeometry.Etale.coefDualizingOpenCompositorPlus`
(node `lem-coef-dualizing-open-compositor-plus`). Zero holes remain in the item;
one remains in the delivery. This is a decomposition, with net zero holes closed.
The new theorem is strictly the bounded-below clause of the original conjunction.
The geometric and counit clauses, including both coefficient levels, are proved.

## No longer needed

Removed redundant private imports `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`
and `Sheaf.AlgebraicGeometry.CompactifiableOverField`. Both remain transitively
available through the unchanged public imports; no modules are withdrawn.
Removed `lem-asd-etale-compact-support-normalization` from the parent's proof dependencies
and top-level tool-use list: the actual open normalization is already constructed.
The bounded-below comparison dependencies are now carried by the new substep node.

## Where the brief, the DAG or earlier work was wrong

The bounded-below clause needs compatibility of the identity direct-image
normalizations in addition to the published compactification and compositor squares.
The new theorem's proof in words gives that argument via derived-unit uniqueness,
then inversion and naturality. Empty opens, identity opens and equal coefficient
levels introduce no exceptions. No statement or definition correction was needed.
Direct assembly of the comparison squares was explored, but kernel checking of
concrete functor conversions exceeded the compile limit. The delivered partial proof
leaves the whole bounded-below step as a named theorem, with the independent geometric
and composite-counit argument complete.

## New nodes

`lem-coef-dualizing-open-compositor-plus` is step 5 of the original node: compatibility
of the specified normalized compositor on bounded-below inputs. It omits the structural
adjoint, evaluation counit, geometric conclusions and two-level coefficient assembly.
The parent proves those clauses and uses this substep at each coefficient level.
The new module also owns the four unchanged comparison definitions. Change record:
`coord/changes/coef-dualizing-open-comparison-location.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
