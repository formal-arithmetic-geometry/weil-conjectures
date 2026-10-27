## What changed

The arbitrary affine presentation is reduced to the single standard global frame of
one explicitly constructed free bundle. The proof uses the existing proved private
`OrientationRefinement.finite_trace_cartesian` through a proof-only `import all`.
Unlike its public wrapper, this proof does not require a zero-preserving map.

`AffineVectorTraceAction` defines compact-support transport with its identity
pullback comparison removed and proves strict composition from exchange pasting,
naturality and ordered Tate composition. `AffineVectorStandardFrame` constructs the
inverse standard free frame from the actual top-open chart, proves its projection
equation and invertibility, and states its normalization separately. This new
module imports finite coefficients and vector integration directly and obtains
compactifications from Nagata, avoiding the broad diagonal-refinement import.

The item composes the given presentation with that fixed inverse frame, applies
Cartesian vector-trace compatibility, and cancels the invertible fixed frame action.
A proved identity-unit calculation restores exactly the original displayed equation.
The original theorem signature and public imports are preserved. The derived-pullback
composition/unit theorem is used only as categorical glue; it does not replace
a unit route. No other existing Lean module or node is changed. The main file locally reuses the canonical
derived-category instances, as in the existing Cartesian trace module, to keep
type checking and linting within the per-file time limit.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.affineVectorTracePresentation`.
Proved `AlgebraicGeometry.Etale.affineVectorTraceAction_comp`, the standard chart's
projection equation and invertibility, and the private identity-unit calculation.

Added one hole:
`WeilConjectures.PurityFiniteSetting.affineVectorStandardFrame`
(node `lem-pur-affine-vector-standard-frame`).
This is a decomposition, one original hole closed and one strictly smaller hole
added, net zero. The remaining assertion has only the canonical free module and
one explicitly constructed standard global frame. It has no arbitrary bundle,
nonlinear scheme isomorphism or zero-section translation. The combination proof
handles all arbitrary presentations and is complete. The item has zero holes;
the packet has one hole.

Server compilation passed without warnings for all three modules: transport
composition in 31 seconds, standard-frame normalization in 42 seconds, and the
final main file in 21 seconds. The original theorem signature was compared
verbatim with the current repository source and is unchanged.

The standard-frame statement was checked at rank zero, on the empty base and for
the zero coefficient ring. The concrete free module and top-open isomorphism
exist in each case, and only the same normalization and unit identities are used.

## No longer needed

The implemented route does not use `lem-trf-ambient-affine-translation-trace`
(`Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace`) or
`lem-pur-affine-translation-trace` (`Sheaf.Paper.AffineTranslationTrace`).
The Cartesian trace proof already accepts nonlinear bundle maps without requiring
zero preservation, so there is no need to move the image of zero by translation.
The latter module also reaches the item, so importing it here would make a cycle;
the fixed free module is used directly rather than importing its downstream alias.

The direct planned use of `lem-pur-vector-normalized-trace-cartesian` is replaced
by the existing private generalized proof in the same module. Its actual inputs
are normalized vector purity, its base-change law, its unit adjunct and ordered
Tate square compatibility, recorded in the item node's updated dependencies.
Ordered coefficient composition and twist-transport uniqueness remain needed.
No original public import is removed, no source-library declaration is deleted,
and no whole-library module withdrawal is claimed. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan unnecessarily required translation and zero preservation.
Reading `VectorNormalizedTraceCartesian` showed that `finite_trace_cartesian`
proves the trace equation for every Cartesian presentation; the public wrapper's
zero-preserving hypothesis is unused. This delivery neither changes that wrapper
nor adds a new unproved general invariance claim.

The item docstring and node now describe the implemented cancellation argument
in place of the longer translation argument.
The remaining standard-frame normalization is the local normalization at the
fixed global frame with its top-open transport made explicit, a strict part of
that argument rather than the original theorem under another name.

## New nodes

`lem-pur-affine-vector-trace-action-comp`, attached to
`Sheaf.Paper.AffineVectorTraceAction`, records the proved composition calculation.
It concerns only exchange and coefficient transport, with no integration map.

`lem-pur-affine-vector-standard-frame`, attached to
`Sheaf.Paper.AffineVectorStandardFrame`, records the one remaining normalization
at the explicit standard global free frame. Its docstring and node give the
normalization, top-open base-change and coefficient-pasting proof in words.
There are no shared-interface change records or forced adaptations.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
