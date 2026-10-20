## What changed

Completed the ordinary closed-support coefficient adjunction, the coefficient tensor
factorization, its signed total-complex extension, unique derived descent, and the
identification with the existing external product. The supported exterior product,
its evaluation counits and the finite-coefficient transport keep their construction.

The ordinary adjunction is constructed from the existing adjunctions. Its prescribed
quotient normalization follows by identifying the supported global sections kernel
with the kernel of restriction to the complementary open. Cancellation of the
coefficient quotient proves uniqueness. The tensor target vanishes on the actual
two-open cover of the complement of the product support, giving its factorization.

Added two fully proved independent results: closed direct image preserves flat
pro-etale module sheaves, and a natural tensor comparison of exact functors descends
uniquely when the second functor preserves flat objects and is a left adjoint. The
latter module also provides the signed total-complex comparison and its summand API.
It uses the source library's derived bifunctor universal property. Its argument
follows the same universal-property construction used by the private comparison
proof in the etale supported-product module; it does not depend on that private API.

Five definition refactorings have change records. Shared generic morphism and
condition interfaces avoid repeated expansion of the derived monoidal construction.
The derived condition retains the curried-tensor morphism composition and the final
map identifying the complex tensor with the signed total tensor. The generic proof
explicitly proves the latter is an identity; it is still present in the condition.
The chosen derived morphism keeps its original public return type. It casts the
uniquely specified family along
`supportedCoefficientTensorDerivedHom_tensor`, using `supportedTensorHom_eq`; the
identified types are definitionally equal. No target signature or adopted
source-library file changes.

The external-product equality uses proved structural heterogeneous congruence to
identify the implicit categorical data without repeatedly unfolding the large
monoidal model. The specialization to module coefficients uses an explicit equality of proposition
types, proved by the same congruence, including the canonical braided/symmetric
instance identification. Its generated proof is checked by the ordinary Lean kernel.

Validation: all three delivered modules compile cleanly; the item compiled in
43.2 seconds. The unchanged consumers `Sheaf.AlgebraicGeometry.SupportQuotientProduct`,
`Sheaf.AlgebraicGeometry.SupportedProductQuotientModel`, and
`Sheaf.Paper.SupportedHomAdjunctionTranspose` compile against the completed item
in the same sandbox import-order compile. Their temporary copies are not delivered.

## Proved and sorry left

Five original holes closed, by declaration:

- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientAdjunction`
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensor`
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensorComplex`
- `AlgebraicGeometry.ProEtale.exists_unique_supportedCoefficientTensorDerived`
- `AlgebraicGeometry.ProEtale.supportedExternalProduct_eq`

Zero holes added or split off. Zero holes remain in the three delivered modules.
The two new nodes have complete Lean proofs. This is a proof delivery, not a
relocation of holes into new hypotheses or intermediate statements.

## No longer needed

No node or module is withdrawn. The existing unit route is preserved. The item's
previous recorded proof had no proof dependencies to prune. The new proof uses the
existing closed/open support and monoidal inverse-image results, together with the
two proved nodes listed below. New imports used only by proofs are private imports.

## Where the brief, the DAG or earlier work was wrong

The prior node proof recorded only W4's auxiliary exactness and complex identities,
not the remaining five constructions. The updated route records their proofs.
The current blueprint source is under `sk-prop-an`, while the inherited source and
proof-origin paths used `sk-prop-a1-kummer`. The immutable inherited source record
is retained; the new proof origin points to the current source.

The derived proof needs existence and uniqueness of a normalized comparison, which
follows directly from the universal property of a derived bifunctor. It does not
need a separate theorem that the coefficient comparison is an isomorphism. The
statement being proved specifies a morphism, naturality and model normalization.
Empty schemes, empty or whole supports, the zero ring/module and unbounded complexes
are admitted: the complementary restrictions and covering arguments are categorical,
and derived descent uses functorial K-flat resolutions rather than boundedness.

No forced adaptation of another group's module is included.

## New nodes

- `lem-pur-proetale-closed-pushforward-flat`, module
  `Sheaf.AlgebraicGeometry.ProEtaleClosedPushforwardFlat`: fully proved.
- `lem-pur-derived-tensor-comparison`, module
  `Sheaf.CategoryTheory.DerivedTensorComparison`: fully proved, including its
  complex comparison API and model normalization.

Definition change records: `coord/changes/Y3-supportedCoefficientTensorComplexHom.md`,
`coord/changes/Y3-supportedCoefficientTensorComplexCondition.md`,
`coord/changes/Y3-supportedCoefficientTensorDerivedHom.md`,
`coord/changes/Y3-supportedCoefficientTensorDerivedCondition.md`, and
`coord/changes/Y3-supportedCoefficientTensorDerived.md`.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
