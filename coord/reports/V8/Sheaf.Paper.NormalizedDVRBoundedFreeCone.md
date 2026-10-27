## What changed

Replaced the hole in `WeilConjectures.normalizedDVR_bounded_free_cone` by explicit
homotopy-limit transport and adjunction naturality. The given Roos triangle gives
a cone with vertex exactly M. The compatible eU identify its tower with the
one-step tail of U. The proof applies a localized scalar-cone functor to the
(n+1)-step tail and transports its representative comparison to the requested
multiplication-cone tower.

Added `Sheaf.Algebra.Homology.LinearScalarCone`: the diagonal cone on complexes,
a proved quasi-isomorphism-invariance theorem, explicit augmentation maps, and its actual universal
localization and canonical comparison. No object is chosen from an unproved
existence theorem. Added two strictly simpler residual statements separating
scalar-cone exactness/products from the coefficient augmentation calculation.
The original theorem signature is unchanged. No existing definitions or other
modules were adapted. The original public imports stay; the three new proof
imports are private. The new augmentation module does not import the separate
`DerivedLimit` interface, which its statement does not use.

## Proved and sorry left

Original holes: 1, in `WeilConjectures.normalizedDVR_bounded_free_cone`.
The hole is closed by a complete proof from the two residual statements.
`CochainComplex.LinearScalarCone.inverts` is proved, as is the private
Roos-triangle/cone bridge. No sorry remains in the assigned module.

Added holes: 2. This is a decomposition, not a net proof gain.

- `CochainComplex.LinearScalarCone.exact_products`
  (`lem-coef-linear-scalar-cone-exact-products`): generic exactness and product
  preservation of a fixed localized two-term scalar cone. It mentions neither
  the DVR tower nor its homotopy limit or augmented projection.
- `WeilConjectures.normalizedDVR_roos_augmentation`
  (`lem-coef-normalized-dvr-roos-augmentation`): the coefficient interpretation
  and its single augmented projection equation on the canonical Roos object.
  It asserts no homotopy-limit preservation and constructs no cone for the
  multiplication-cone tower. The main proof supplies those parts using the
  generic lemma and actual tower/adjunction transport.

Each residual declaration has its source, complete proof in words, edge-case
checks and a new node. The scalar-cone definitions contain no holes.

## No longer needed

No original public import is removed. No module is withdrawn. No existing
statement dependency is pruned: the statement still fixes the same interfaces.

The main proof does not use the following old proof dependencies directly:
`lem-weil-proetale-countable-products-exact`,
`lem-weil-derived-limit-products-core`, and
`def-pc-tensor-complex-sheaves`. Countable products are an existing hypothesis;
the scalar cone preserves them as a right adjoint, so no termwise derived-product
calculation is needed here. These nodes remain in the library and may still be
needed by other parents.

The regularity, projection divisibility, principal Koszul replacement and regular
quotient augmentation nodes remain needed by the new augmentation sublemma;
they have not been pruned from the argument. The scalar adjunction and strict
normalized-adic interface remain in the statement and the new sublemma.

## Where the brief, the DAG or earlier work was wrong

The local read-only mirror initially lacked the assigned Lean file and its
FlatCokernel dependency despite having their DAG records. There was no matching
quarantine/rework entry. The current assigned file was read from the project
meeting point; lcompile supplied the unpublished FlatCokernel dependency in its
private overlay. No archived file or declaration was deleted.

The old plan required computing derived products termwise. For this bounded
scalar cone that is stronger than necessary: finite duality gives product
preservation directly. The node now records the route actually used.

## New nodes

`def-coef-linear-scalar-cone` records the explicit scalar-cone functor and its
proved localization construction in `Sheaf.Algebra.Homology.LinearScalarCone`.

`lem-coef-linear-scalar-cone-exact-products` is the generic bounded-free
exactness/product step, with no DVR effectivity conclusion.

`lem-coef-normalized-dvr-roos-augmentation` is the separate regular-quotient
and normalized coefficient-augmentation step. It has no output homotopy-limit
cone and no assertion that the scalar-cone functor preserves such limits.

There are no change records because no existing statement or definition changes.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
