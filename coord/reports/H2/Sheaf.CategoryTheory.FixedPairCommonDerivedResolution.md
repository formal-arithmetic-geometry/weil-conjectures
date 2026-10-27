## What changed

Proved `CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_commonDerivedResolution`
in `Sheaf.CategoryTheory.FixedPairCommonDerivedResolution` with its signature and all
three existing resolution constructions unchanged. The proof follows the node's six
steps. Existing instances provide additivity, preservation of finite limits and
preservation of quasi-isomorphisms and K-injectives. The Grothendieck-abelian resolution
instance supplies the two existence witnesses.

Added the proved private helper `resolutionIso_naturality`: unfold the canonical
resolution isomorphism at the identity, apply naturality of the quotient-to-derived
comparison, inverse-unit naturality, and the target quotient comparison. Applying this
helper to transport and to the underlying functor, followed by exact-forgetful
comparison naturality, proves the two actual conjugation equations. This is step 6
of the existing node, not a new mathematical dependency or a changed proof route.

Single-file remote compilation passed without warnings (5.4 seconds before removing
the redundant import; the final delivery checks validate the final file).

## Proved and sorry left

Closed 1 hole: `CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_commonDerivedResolution`
(node `lem-sf-fixed-pair-common-derived-resolution`). The private naturality helper is
also completely proved. Remaining holes in the item: 0. Added holes: 0. Split off: 0.

## No longer needed

Removed the redundant private import `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
Its declarations remain available through the existing public import of
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`, which uses the
K-injective total-derived theorem to define the chosen universal pair. Thus no DAG
node or mathematical module is pruned: all six recorded proof dependencies remain
used, directly or through the existing resolution-isomorphism API. No public imports
were removed.

## Where the brief, the DAG or earlier work was wrong

None. The existing definitions and proof dependencies suffice, and the unit route is
preserved. No statement or definition repair, new nodes, or consumer adaptations are
needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
