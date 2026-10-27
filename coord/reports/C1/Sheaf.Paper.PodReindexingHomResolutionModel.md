## What changed

Proved `WeilConjectures.podReindexing_roundTrip_shift` in
`Sheaf.Paper.PodReindexingHomResolutionModel`. Private proved helpers establish
constant and completed coefficient round trips, the module equivalence with its
specified section maps, functor equality after derived localization, and the finite
pullback comparison. Added the private proof import
`Sheaf.AlgebraicGeometry.ProEtale.FiniteComparisonIsomorphism` with `import all`
to use its proved, section-normalized finite adjunction. Public statements,
definitions and public imports are unchanged. Updated the item's node proof for
Steps 3 and 11 and recorded the finite comparison dependency.
The completed proof passed server single-file compilation in 34 seconds; the
unused private existential binder names were then prefixed with underscores.
Both the Lean import cycle check and the node dependency cycle check pass.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.podReindexing_roundTrip_shift`.
Added zero holes and split off zero statements.

The only remaining hole is the untouched
`WeilConjectures.podReindexing_hom_resolution_model`, attached to
`lem-pod-reindexing-hom-resolution-model`. The existing completed proofs of
`podReindexingCoefficient_existsUnique` and
`podReindexing_resolution_preservation` are preserved.

## No longer needed

None. No imports, nodes or modules are withdrawn. The dependencies of the remaining
Hom-resolution proof plan remain needed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was required. The finite derived comparison is obtained by
uniqueness of left adjoints from the section-normalized adjunction, rather than by
claiming definitional equality between the sectionwise functor and the intrinsic
pullback presentation.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
