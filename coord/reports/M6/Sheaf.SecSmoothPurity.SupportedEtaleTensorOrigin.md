## What changed

Filled `AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.proScalarTensorIso_existsUnique`
using the existing ordinary balancing projection, the exact-right-adjoint K-flat representative
comparison, and uniqueness of left derived functors. Private helpers construct the tensor
counit, prove its K-flat invertibility, and apply the left-derived universal property.
The chosen isomorphism satisfies the original normalization on every cochain complex;
uniqueness follows from `Functor.leftDerived_ext`. Public statements and definitions are
unchanged. Added only private proof imports. Local transparency settings keep the
chosen adjunction and ordinary coefficient comparison folded during elaboration. The existing
main theorem uses explicit existential/conjunction constructors for the same witnesses.
The full file compiled in 50.8 seconds before the final explicit simp-list cleanup;
`deliver3.py` reruns the final compilation and preflight.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.proScalarTensorIso_existsUnique`
(node `lem-sp-supported-etale-tensor-origin`). No holes added; zero local holes remain.
The already proved supported-origin theorem and balancing naturality are retained.
This is one proof, not a decomposition.

## No longer needed

No nodes or modules are withdrawn. No declared dependency of the existing supported-origin,
Tor-amplitude, or open-mate proof is bypassed. The new comparison proof uses the original
K-flat route. The separate etale scalar/tensor existence theorem is not used to prove the
pro-etale one; its existing use by `etaleScalarTensorFamily` remains.

## Where the brief, the DAG or earlier work was wrong

The file has one remaining hole, rather than the three in its historical stage-2 record.
The earlier D4 delivery already proved balancing naturality and the main supported-origin
theorem. The node now records the proof of the remaining comparison theorem instead of
saying its original hole is retained. No mathematical statement was changed.

The generic theorem `lem-sfb-exact-right-adjoint-kflat-representative` is used as a tool:
it applies to this chosen derived adjunction without changing the unit route. Its Lean
module is `Sheaf.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative`. The ordinary
projection is the already proved `ProEtale.isIso_sheafExtendScalarsProjection`; derived
uniqueness and extensionality are Mathlib. The proof needs no finite Tor dimension of B,
and includes the zero-ring, zero-complex and nonflat coefficient cases.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
