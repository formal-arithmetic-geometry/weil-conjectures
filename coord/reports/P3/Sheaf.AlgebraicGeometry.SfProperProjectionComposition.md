## What changed

Proved `AlgebraicGeometry.Etale.SupportedTrace.properProjectionCompositionOfEq`
in `Sheaf.AlgebraicGeometry.SfProperProjectionComposition`, following its existing
DAG proof plan. Added a proof-only `import all` of
`Sheaf.AlgebraicGeometry.ShriekTensorComposition` to use its proved private
`projectionMap_chosen_comp` calculation. No public signature, definition or import changed.

After eliminating the equation identifying the composite, the proof identifies
`unboundedEtaleLowerShriekCompIso.hom` with
`rightDerivedLowerShriekCompIso.inv` by expanding just their three comparison
factors. It rewrites the existing projection square, cancels the final inverse
compositor, and cancels the tensor of the inverse compositor. The projection
isomorphisms have exactly the underlying canonical projection maps.

The categorical cancellation is proved in private helpers for arbitrary
categories and a bifunctor. The imported square is used with its local tensor
instance conventions and with explicitly written derived pullbacks. The final
conversion to `projectionIso` and `CoordinateTrace.pull` uses congruence and proof
irrelevance, keeping large derived constructions folded. The conversion retains explicit equations for the wrappers and caches
congruence comparisons. Its auxiliary proof constants are checked separately by
the kernel. Instance changes are scoped to individual private declarations or
their section. The node's proof
text records these implementation details; its mathematical dependencies are unchanged.

Validation: the final module compiled through `lcompile.py` in 18.7 seconds,
with no warnings, profiling options, heartbeat overrides or unfinished proofs.
The existing public theorem's signature and docstring remain verbatim.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Etale.SupportedTrace.properProjectionCompositionOfEq`
(node `lem-sf-proper-projection-composition`). No holes added or split off.
No `sorry` remains in the delivered module. No intermediate obligations were introduced.

## No longer needed

None. The proof uses the one declared proof dependency,
`lem-amb-shriek-tensor-composition`, through its existing chosen-compactification
projection calculation. No existing import, node or module was removed or withdrawn.
The unit's statement and proof route are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The stated plan already supplied the
necessary projection square and the precise inverse relation between the two
compositors. Its private calculation is accessible with a proof-only `import all`;
there is no need to expose a new API or split the obligation again. Concrete
coefficient instance conversions required private congruence helpers; a blanket
`simp` conversion forced the kernel to unfold the large derived constructions.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
