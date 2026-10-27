## What changed

Proved `AlgebraicGeometry.finite_affine_composite_presentation` in
`Sheaf.AlgebraicGeometry.FiniteAffineCompositePresentation` without changing its statement.
Constructed the two maps by `Sigma.desc`, the canonical spectrum isomorphism by
`Sigma.mapIso` and `sigmaSpec`, and both ring maps by `RingHom.pi`.
A proved private helper identifies the coordinate maps by testing every coprojection
and using `Scheme.Opens.toSpecΓ_SpecMap_appLE`. Restriction/composition identities give
compatibility. Source locality gives local finite presentation of the coproduct map;
`LocallyOfFinitePresentation.SpecMap_iff` then gives finite presentation of the product
ring map. Updated the item's proof plan to record these Mathlib APIs.

All hypotheses and public imports are preserved. The proof treats empty index types
and zero rings uniformly; it neither chooses a component nor assumes a nonzero ring.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.finite_affine_composite_presentation`
(node `lem-trf-finite-affine-composite-presentation`).
Zero holes remain and zero holes were added. The private helper `sigma_desc_spec`
is proved in full. No split-off statements.

Validation: the single-file server compile completed in 8.5 seconds without errors or warnings.
The delivery preflight independently checks the declarations and their axioms.

## No longer needed

None. All seven declared proof dependencies are Mathlib definitions or leaves used
by this proof. No modules, nodes, or imports are removed. The final application of the
affine criterion uses `SpecMap_iff` after transport by the canonical isomorphisms,
avoiding explicit whole-open coordinate transports without removing a dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The final affine-criterion step is implemented through
Mathlib's equivalent spectrum-map criterion. The unit's statement and realized steps
are unchanged. No shared interfaces or consumer modules are changed.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
