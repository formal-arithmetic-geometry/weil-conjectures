## What changed

Completed the six proof obligations in `Sheaf.Paper.PurityAffineLineDatum` without changing
any existing signature or definition. The coefficient-map witness is the existing
`AlgebraicGeometry.Etale.ordinaryFiniteRootMap`; equality on sections gives uniqueness.
The root-pullback witness is the published kernel comparison, with uniqueness by its
monic kernel inclusion.

Private, fully proved helpers compose sheafification and extension/restriction of scalars
adjunctions. Additive maps out of the exponent-torsion roots are automatically ZMod-linear.
The inverse-image adjunction and the canonical forgetting comparison transport this
universal property to pulled-back roots. It proves existence and uniqueness of the twist
pullback. The existing invertible-exponent roots pullback theorem, together with these
Hom equivalences and the coyoneda criterion, proves that the specified twist map is an
isomorphism. Finally, restriction to the coordinate basic open constructs the punctured
map, and composition with the affine projection proves its square.

Two proof-only imports were added: `WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback`
and `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`. Their generic roots comparison and
root coefficient map are used directly; no projective-line decomposition is used.

## Proved and sorry left

Closed all six original holes (namespace `WeilConjectures.PurityFiniteSetting`):

- `existsUnique_rootCoefficientMap`
- `existsUnique_rootPullback`
- `existsUnique_twistEtalePullback`
- `isIso_twistEtalePullback`
- `existsUnique_puncturedMap`
- `puncturedSquare`

All six realize `def-pur-affine-line-datum`. Zero holes remain in the delivered module;
zero holes were added and no statement was split off. The new private helpers are proved.
Dependencies retain their existing proof status.

## No longer needed

No original import, node or module is removed. The item's node had no proof dependencies
to prune. Its definition and the unit route are retained. The source's local primitive-root
argument for the isomorphism is supplied by the existing upstream roots pullback theorem;
no new local-triviality or cover-descent obligations are introduced.

## Where the brief, the DAG or earlier work was wrong

The inherited sandbox had all six candidate proof bodies but no report or delivery.
Its `pullbackRootExtensionEquiv_apply` proof needed explicit unfolding of `forgetEtale`
and the identity wrapper before simplifying the composite equivalences. No mathematical
statement or definition needed correction. The underlying and scalar-forgotten direct
images are definitionally equal, and the explicit unfolding makes that equality available
to rewriting.

The roots pullback theorem requires `NeZero P.exponent`; this follows from primality of
`P.coefficients.l` and positivity of its power, even at exponent level zero. The arguments
for existence and uniqueness do not require invertibility; only the isomorphism proof
uses `hr`. Empty schemes, identity maps and zero target modules require no extra cases:
the adjunction equivalences and monomorphism cancellation remain valid.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
