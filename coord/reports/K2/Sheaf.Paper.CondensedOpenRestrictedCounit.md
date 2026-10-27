## What changed

Proved `WeilConjectures.CompactSupportCondensedRealization.condensedOpen_restrictedCounit_isIso`
in `Sheaf.Paper.CondensedOpenRestrictedCounit`, with its original statement and public imports.
Added five proof imports and four proved private helpers in the item only. Updated its node's
proof, proof dependencies and proof origin.

The proof lifts the existing abelian clopen-extension comparison to internal modules and derives
clopen ambidexterity. Composition of open adjunctions identifies the restricted supported object.
The section/retraction counit calculation and the existing derived open-restriction mate equation
then prove invertibility. Uniqueness of left adjoints transports it to the specified total-derived
adjunction. The argument works without boundedness or coefficient restrictions; it does not
assume that the original refinement square is Cartesian. Empty opens and identity refinements
are covered by the same categorical argument.

Validation: the complete proof compiled remotely in 25.4 seconds before explanatory comments
were added. The delivery tool performs final compilation and preflight checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CompactSupportCondensedRealization.condensedOpen_restrictedCounit_isIso`
(node `lem-pur-condensed-open-restricted-counit`).

Item holes before: 1. Item holes left: 0. New holes added: 0. Split-off statements: 0.
The four private helpers are completely proved. This is a proof from existing declarations,
including `CondensedRing.derivedOpenRestrictionNormalization`, whose proof remains an existing
separate obligation. No claim is made to close its transitive holes.

## No longer needed

No original imports were removed; all five added proof imports supply declarations used here.
No module is withdrawn or claimed globally pruned.

The former direct proof dependencies `lem-sfb-internal-module-operations-transport`,
`lem-sfb-proetale-open-restriction-counit`, and
`lem-pur-site-restriction-module-adjunction-exact` are replaced at this node by the existing
internal-module derived restriction normalization and by direct lifts of the abelian clopen
comparison. The item does not import their modules directly. They may still be needed
transitively by the normalization theorem or by other consumers.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The plan's section-module equivalence and explicit K-injective
computation can be replaced by existing internal-module derived restriction and categorical
adjunction arguments. In particular, restriction of the counit on the clopen section follows by
factoring the counit of a composite adjunction whose left adjoint is isomorphic to the identity.
There are no changes to shared interfaces, source-library declarations, or the unit route.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
