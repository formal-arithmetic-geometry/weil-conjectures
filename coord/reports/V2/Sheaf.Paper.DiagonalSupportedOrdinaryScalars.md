## What changed

Proved the specified ordinary scalar transpose invertible without changing its
statement, docstring, or public imports. Added two private proof imports:
Sheaf.Paper.CondensedLocallyClosedScalarExtension and
Sheaf.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal, both with `import all`
to reuse their existing proved private helpers.

The closed_scalar_iso helper proves invertibility of the actual closed
scalar/direct-image mate. The regular-module unitComparisonIso is normalized by
unitComparison_unit. A new proved private categorical lemma,
scalar_push_transpose, combines the inverse-mate unit identity with naturality.
It identifies the composite of these two isomorphisms with the exact inverse
adjunct of supportMap, using the supplied underlying-map equality on v.

Updated only the item's DAG proof, proof dependencies, and proof origin to record
this reuse. No shared interface changed and no consumer adaptation is needed.

Remote single-file compilation passed in 8.9 seconds with no warnings. The
original theorem signature and public imports are unchanged. A static transitive
import check shows that both helper modules were already in the original item's
import closure, so the new proof imports add no project modules to that closure.
No profiling options or increased limits remain.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_supported_ordinary_scalars
(node lem-sfb-diagonal-supported-ordinary-scalars).

Zero holes remain in the item. Zero holes were added or split off.
The private scalar_push_transpose lemma is proved in full.

## No longer needed

No original import was removed and no module was withdrawn.
This proof no longer directly needs lem-sfb-internal-section-scalar-adjunction
(Sheaf.CategoryTheory.InternalSectionScalarAdjunction): it stays entirely in the
actual internal module categories and uses their existing scalar adjunctions.
The original dependency lem-sf-ring-sheaf-closed-localization
(Sheaf.AlgebraicGeometry.ProEtaleRingSheafClosedLocalization) is not needed
directly: the already-proved closed_scalar_iso helper supplies the canonical
closed scalar mate using abelian closed support and condensed open/closed
reflection. These are removals of this node's proof edges, not withdrawals of
those modules; existing public imports remain intact.

The sk-prop-diagonal-tower unit's statement and proof route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original restriction calculation is sound, but an earlier delivery overlooked
the proved private closed_scalar_iso helper, available in both
CondensedLocallyClosedScalarExtension and QcqsLatticeTreeReconstruction. Unlike a
bare object isomorphism, it proves that the canonical pushHom comparison is
invertible. Its mate normalization and the existing normalized regular-module
isomorphism suffice to close this obligation without a new intermediate hole.

The proof allows arbitrary nonflat coefficient maps. Zero rings and empty
schemes require no special case: the closed mate helper handles zero
restrictions and the regular-module unit comparison remains an isomorphism.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
