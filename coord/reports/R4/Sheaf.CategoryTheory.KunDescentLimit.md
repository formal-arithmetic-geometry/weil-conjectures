## What changed

Proved `AlgebraicGeometry.kun_descent_limit` in
`lean/Sheaf/CategoryTheory/KunDescentLimit.lean` with no remaining `sorry`s. The proof adds the
private adjunction calculation `homEquiv_paste`, identifies the module transition with
`Etale.AffineLimitSheafApproximation.approximationMap`, proves identity and composition using
upper/lower-star coherence, and transports the existing affine-limit reconstruction colimit
along the opposite-category equivalence. The proof import is
`Sheaf.AlgebraicGeometry.Sites.AffineLimitSheafReconstruction`; `Mathlib.CategoryTheory.Limits.Final`
is used for the final-functor colimit transport. The node copy records the actual proof route.

## Proved and sorry left

Closed the single hole, `AlgebraicGeometry.kun_descent_limit`. No `sorry` was added or left. Holes closed: 1; holes added: 0; split off: 0.

## No longer needed

The proof does not use the previous site-level plan or its imports:
`Sheaf.AlgebraicGeometry.LimitAffineTransition`,
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimitStatement`,
`WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite`,
`WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos`,
`Sheaf.CategoryTheory.SiteCoveringAxioms`,
`WeilConjectures.CategoryTheory.ColimitSiteSections`, and
`WeilConjectures.CategoryTheory.SiteFilteredColimitSections`. The corresponding site-colimit
nodes and the affine-site section computation are not needed because the already-proved
`lem-sc-affine-limit-sheaf-reconstruction` supplies the colimit directly.

The following old direct proof dependencies are pruned from this node:
`def-weil-size-convention`,
`lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-affine-etale-site-topos`, `def-weil-pbc-direct-image`,
`def-weil-pbc-inverse-image`, `def-weil-pbc-sites-and-cohomology`,
`lem-weil-pbc-affine-morphism-permanence`,
`lem-weil-pbc-abelian-etale-sheaves-grothendieck`, `def-weil-pbc-category-colimit`,
and `lem-weil-pbc-colimit-of-sites-sections`. Definitions of inverse and direct image
remain statement dependencies. The unused old tool approvals for affine-transition limits,
affine-site colimits, affine-site toposes, Grothendieck abelian sheaves, and colimit-site
sections are removed; the inverse-image composition approval is retained.
These are removals from this node's direct route, not claims that all these modules
leave the targets' transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The imported DAG proof plan was substantially longer than necessary: the library already
contains the arbitrary-abelian-sheaf affine-limit reconstruction theorem, so the torsion and
site-equivalence argument can be replaced by its direct application. The target statement and
all public signatures are unchanged.


The existing `lem-sc-affine-limit-sheaf-reconstruction` and
`def-sc-affine-limit-sheaf-approximation` serve as tools from the adjacent cbc unit.
The Künneth unit record has no realized steps imposed on this node, so using the existing
reconstruction theorem preserves its statement and route. No new node or change record
is needed: both definitions and the public theorem signature are unchanged.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
