## What changed

Proved CategoryTheory.RoosConeCalculus.roos_cone_calculus using the existing strict
roosF. Its public coordinate definitions, theorem signature, docstring and public imports
are unchanged. All added constructions and helpers are private and proved.

The proof constructs the signed double-cone permutation and its inverse, checks the
chain-map equations, and proves naturality, cone inclusion, boundary and augmentation
compatibility. ProductCommShift and SignedMappingCoconeShift give the coherent shift,
transported to roosF through the identity-component natural isomorphism. Homology
preservation of exact products proves the product quasi-isomorphism assertion; localized
cone triangles then prove it for roosF. DerivedCountableProductsCore supplies the actual
localized product cone, and its projection-preserving comparison transports the Roos
triangle to the chosen derived product.

Added five private proof imports: ProEtaleProductsExact, DegreewiseLimits,
DerivedCountableProductsCore, SignedMappingCoconeShift and ProductCommShift. Updated the
node's proof, proof dependencies, proof origin and obsolete tool-use entry to match.
There are no new public declarations, new nodes, definition repairs or source-library edits.
The local command scopes are documented in
coord/changes/H3-roos-cone-calculus-local-proof-scopes.md; downstream.py reports zero
current Lean importers, and no consumer is adapted.

The complete module passes lcompile.py without errors or warnings (33.2 seconds).
The delivery tool performs the remaining preflight checks. Product, cone and shift constructions have explicit coordinate APIs and become
locally irreducible after those APIs. For the final sheaf-module specialization, local
irreducibility of roosF/roosConeFunctor and scoped transparency settings prevent expansion
of their construction while elaborating the unchanged statement. No timeout was raised,
no module was split, and no launcher script or publication state was changed.

## Proved and sorry left

Closed the original single hole in
CategoryTheory.RoosConeCalculus.roos_cone_calculus (lem-pe-roos-cone-calculus): 1 of 1.
Remaining holes in the item: none. Holes added: zero. Split statements: zero. Every new
private helper and construction is proved; no sorry occurs in the delivered Lean file.

## No longer needed

Removed these four dependencies from this node's proof route:

- lem-pe-endomorphism-fibre-coordinate-calculus: the existing strict Roos coordinates
  give the required differential, map and augmentation equations directly.
- lem-pe-endomorphism-fibre-double-cone: the explicit permutation and inverse prove
  the double-cone calculation directly.
- lem-pe-roos-coordinates-quasi-iso, module
  Sheaf.Algebra.Homology.RoosCoordinatesQuasiIso: localized cone triangles and shift
  invariance prove the quasi-isomorphism assertion.
- det-pe-products-derived, module Sheaf.AlgebraicGeometry.ProEtaleProductsDerived:
  det-pe-products-exact and lem-weil-derived-countable-products-core suffice for the
  countable product here. Removed its obsolete tool-use entry as well.

No original public import was removed. There are no module withdrawals or source
library declaration removals. The unit route and target statements are preserved.

## Where the brief, the DAG or earlier work was wrong

The retained attempt was unfinished and uncompiled. The former unknown-Sheaf-prefix
failure no longer reproduces; existing imports compile once the publication gate is open.
The former proof plan used stronger product results and separate coordinate comparisons
than this proof needs. No mathematical statement correction is proposed. The slow final
specialization came from unfolding the concrete functor during elaboration; scoped
transparency and the private coordinate APIs resolve it without changing its definition.

The first completed-proof preflight requested a change record for the added file-local
commands (gate d). The record above documents their scopes and unchanged public
interface; no Lean proof change or permission exception was needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
