## What changed

Replaced the hole in AlgebraicGeometry.ProEtale.EvenLineProduct.evenLineProductIntegrationSymmetry
by tensor-power induction, binary-tree induction, explicit permutation recursion, and cancellation
of the specified projection map. The original public statement and public import stay unchanged.
Four private proof imports expose strictly smaller concrete comparison obligations in new modules.
The DAG proof now records these arguments and their dependencies.

The unit-object hypothesis makes the canonical self-braiding of the integrated line the identity.
Naturality reduces this to the tensor unit, where braiding/unit compatibility and monoidal
coherence identify both unitors. Consequently every recursively defined signed tensor permutation
of that object is the identity. Cancelling kappa in the geometric intertwining square shows that
coordinateAction itself is the identity, so any supplied J is invariant. Projection naturality
and projection_isIso similarly give coefficientAction=id. The given trace need not equal the
assumed object isomorphism to the unit.

## Proved and sorry left

Closed the whole-proof hole of
AlgebraicGeometry.ProEtale.EvenLineProduct.evenLineProductIntegrationSymmetry by a decomposition.
Tensor-power recursion, normalization of arbitrary trees from the binary equation, invertibility
conclusions, finite-permutation identity calculations, the even integer sign calculation, and
projection cancellation are proved in this delivery.

Added four holes, each the complete proof of one public theorem in its own module:

- AlgebraicGeometry.ProEtale.EvenLineProduct.binaryProductNormalization
  (lem-pur-even-line-binary-product-normalization): binary products in kappa coordinates.
- AlgebraicGeometry.ProEtale.EvenLineProduct.coordinateIntertwining
  (lem-pur-even-line-coordinate-intertwining): the geometric permutation intertwining square.
- AlgebraicGeometry.ProEtale.EvenLineProduct.evenTateLineSelfSymmetry
  (lem-pur-even-tate-line-self-symmetry): the single shifted Tate line's self-braiding.
- AlgebraicGeometry.ProEtale.EvenLineProduct.coefficientProjectionNaturality
  (lem-pur-even-line-coefficient-projection-naturality): the forward projection square.

Original holes: 1; original holes replaced: 1; new holes: 4; item-module holes remaining: 0.
This is a decomposition, not a net sorry reduction. No definition or instance was changed.

## No longer needed

No existing Lean import was removed and no module was withdrawn.
lem-pur-affine-space-product-domain is not needed: hprod and hV already supply product
invertibility and constructibility. The other geometric dependencies of the old plan are now
localized to the four smaller obligations, not globally unnecessary. The finite compact
projection theorem and finite-Tor site comparison are not reapplied here: the existing
projection_isIso in EvenLineProductIntegrationMaps provides that conclusion. Accordingly removed
the obsolete top-level tool_uses entries lem-weil-finite-compact-projection-formula and
det-pe-finite-tor-comparison-noetherian, retaining the order of all other approvals. Those modules
remain reachable where existing consumers need them. No source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The geometric dependencies use general products, origin witnesses and compactification
coordinates; the item uses a specific affine model and fixed-scalar presentation. Matching them
requires comparison arguments. The new obligations state those arguments without adding purity,
duality, coordinate invariance, abstract six-functor data, or invertibility of the trace.
The braiding part shortens using the already assumed object isomorphism U to the unit and
naturality of the canonical braiding. No unit or chapter route changes.

Edge cases checked: r=0 is one factor, a=b=0 is the first inverse-product equation, and leaf
normalization is the identity. The empty scheme and zero objects do not obstruct cancellation:
all cancelled maps are specified isomorphisms. Tate self-interchange uses a flat rank-one sheaf
in degree -2, giving sign +1 without choosing a global trivialization. K stays first throughout.

## New nodes

lem-pur-even-line-binary-product-normalization records the normalized binary equation. Its proof
uses finite triple normal forms, equality of ordinary triple transposes, and open normalization,
then induction on the second block. Tree assembly remains proved in the item.

lem-pur-even-line-coordinate-intertwining records geometric adjacent-swap/permutation assembly
in the specified coordinate model. It uses binary normalization, finite forward symmetry, and
even Tate self-interchange, and says nothing about J or coefficients.

lem-pur-even-tate-line-self-symmetry isolates the flat rank-one representative calculation:
degree-zero local commutativity and the degree (-2,-2) Koszul factor. No compact support or kappa.

lem-pur-even-line-coefficient-projection-naturality records the forward projection square under
a coordinate automorphism. Projection/exchange coherence and compactification comparison
supply it. It assumes no trace and no invariance of any action.

All four have proof docstrings, current blueprint source places, Lean attachments, and Mathlib
searches. No change record is required: existing signatures, definitions, instances, visibility
and public imports are unchanged.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
