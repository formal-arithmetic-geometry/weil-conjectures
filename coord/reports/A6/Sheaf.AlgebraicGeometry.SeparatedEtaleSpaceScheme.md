## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_separated_etale` in
`Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme`, with its signature unchanged.
The proof follows the stated 03XU/03XX route, using
`chartwise_isLocallyQuasiFinite_of_etale` and
`exists_scheme_of_separated_locally_quasi_finite`.

The represented identity object of `Sch/X` is terminal. The proof compares the
presheaf product with the relative pullback, transports the given closed-diagonal
scheme tests through that isomorphism, and applies the representability theorem.
For the resulting representing isomorphism, every scheme test is explicitly
represented by the test scheme and its identity projection. That proves it is an
étale chart, so the original chartwise assumption proves the structure map étale.
The empty space and arbitrary non-quasi-compact spaces require no extra assumptions.

Replaced the proof-only properness import with
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal`. Kept all public imports
and both proof-dependency imports. Updated the existing node's proof, proof_deps,
and proof_origin to describe this Lean proof. No definitions, statements,
visibility, or consumers changed.

Validation: the item compiled through `lcompile.py` in 5.8 seconds with no diagnostics.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_separated_etale`
(node `lem-a1-separated-etale-space-scheme`).

No holes remain in the item, no holes were added elsewhere, and no statements were
split off. This is a proof from the existing declared dependencies; those
imported lemmas retain their separate proof obligations.

## No longer needed

Removed proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Proper` and removed
`def-weil-proper-morphism` from this node's proof dependencies. The diagonal
hypothesis is transported directly as an `IsRepresentableWith` scheme-test
property, so no scheme-level properness or separatedness declaration is used.
Both `lem-a1-etale-space-locally-quasi-finite` and
`lem-a1-separated-locally-qf-space-representable` remain needed. No other planned
nodes or modules were pruned; no public imports were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. Two elementary interface identifications
were needed: the presheaf product and the pullback over the represented terminal
object are isomorphic, and `yonedaEquiv` agrees propositionally with
`yoneda.preimage`. Both are proved in the item without new lemmas or holes.

The resumed sandbox initially contained only dispatcher metadata, and the shared
delivery log had no delivery for this item, so there was no interrupted proof or
push to repeat. The original sandbox budget was preserved.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
