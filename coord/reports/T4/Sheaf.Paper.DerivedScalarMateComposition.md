## What changed

Only `lean/Sheaf/Paper/DerivedScalarMateComposition.lean` and its existing DAG node
are changed. Seven of the nine original theorem holes are filled. Five proved
private helpers identify the canonical restriction comparisons, implement the
iterated-mate argument, and construct the sectionwise ordinary identity.

Added proof imports `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
and `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The former supplies the unique sectionwise comparison, invertibility of its
geometric inverse mate, and compatibility of the derived adjunctions. The latter
supplies localization's inverse-isomorphism identity. Existing public signatures,
definitions and public imports are unchanged.

The scalar invertibility proof takes a shorter route: successive geometric and
scalar mates are conjugation under composite adjunctions, so invertibility follows
from the restriction/direct-image isomorphism. It does not need the planned
K-flat normalization argument. The ordinary identity construction is the
`pushforwardCongr₂` construction also used in
`Sheaf.AlgebraicGeometry.RingedRestrictionExchangeOpenDescent`, reproduced locally
to avoid importing that module's unrelated assertions.

## Proved and sorry left

Closed 7 original holes (all names have prefix
`AlgebraicGeometry.DerivedScalarMate.`):

- `Edge.restrictionSquare_existsUnique`
- `Edge.action_isIso`
- `Edge.scalar_isIso`
- `Edge.comp_compatible`
- `identity_compatible`
- `identity_direct_existsUnique`
- `commuting_square`

The last is proved from `derived_scalar_mate_composition`, as intended by the
node: cancel the B-compositors, then transport the composite beta by equality
induction on the equality of Edges. It is not an independent proof of composition.

Two original whole-theorem holes remain, both belonging to the unchanged node
`lem-sfb-derived-scalar-mate-composition`:

- `AlgebraicGeometry.DerivedScalarMate.normalization`
- `AlgebraicGeometry.DerivedScalarMate.derived_scalar_mate_composition`

Added 0 holes, split off 0 statements. No new modules or nodes. No definition has
a new proof hole. This is a partial proof delivery; the K-flat representative
normalization and the composition/identity calculation are still outstanding.

## No longer needed

None. No imports, declarations, modules or dependency nodes are withdrawn.
The K-flat normalization dependency is unnecessary for `Edge.scalar_isIso` after
the double-mate argument, but remains needed for the remaining normalization and
composition obligations. The existing unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The auxiliary invertibility proof plan was longer than necessary: it invoked
balanced tensor normalization and K-flat resolutions, whereas compatibility of
the existing geometric restriction adjunctions and the iterated-mate/conjugation
identity already suffice. The theorem docstring and DAG now record that route.
No statement was disputed or weakened. No shared interface was changed.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
