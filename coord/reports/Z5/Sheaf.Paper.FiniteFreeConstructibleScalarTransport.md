## What changed

Proved `finiteFreeConstructibleScalarTransport` by transporting the supplied local models.
The proof preserves both strict term bounds, uses the tensor-product finite/projective
instances degreewise, proves K-flatness of the realized model from bounded site-flatness,
and makes the published model morphism invertible through its normalized K-flat counit.
The same proof also constructs the local models needed for target membership.

The actual-ring local-perfect criterion is stated separately in
`Sheaf.Paper.IntegralPadicLocalPerfectCriterion`. It is a one-coefficient formulation of
Bhatt--Scholze Proposition 6.6.11; it does not assert scalar-extension preservation or
identify the specified scalar model morphism. Its forward and reverse directions are
combined with the independently proved transport calculation in the assigned module.

The ordinary balancing isomorphism is constructed from the composite tensor/restriction
adjunctions. The coefficient square is proved by its finite quotient projections; the
left-adjoint uniqueness equation normalizes the comparison at the terminal object,
restriction gives every pro-etale object, and linearity gives arbitrary tensor sections.
The same adjunction detects equality, proving the required uniqueness.

All existing public declaration signatures, definitions, and public imports are preserved.
No source-library module is changed. The elaboration attributes required by the new
proof are recorded in `coord/changes/z5-finite-free-proof-attributes.md`.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.finiteFreeConstructibleScalarTransport`.

Closed: `AlgebraicGeometry.Scheme.finiteFreeConstantBalance_existsUnique`.
Its coefficient-square calculation, adjunction construction, section normalization,
and uniqueness are proved, with no replacement balancing obligation.

Added one separate hole:
`AlgebraicGeometry.Scheme.integralPadicLocalPerfectCriterion`.

Both of the two original holes are closed; one separate characterization hole is added.
The membership argument is a decomposition through this strictly separate criterion;
the balancing hole is proved without an added obligation. The coefficient-complex bounds, finite
projectivity, realized K-flatness, and invertibility of the prescribed local-model map
have complete Lean proofs. No holes occur in private helpers or definitions.

Validation: single-file and import-ordered server compilation via `lcompile.py`;
final delivery compilation and preflight are run by `deliver3.py`.
Edge cases checked in the argument: zero terms, the zero complex, empty strata,
identity coefficient extension, and unchanged (possibly nonoptimal) strict bounds.

## No longer needed

Removed the proof imports `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`,
`Sheaf.CategoryTheory.RingedSiteDerivedRestrictionUniverses`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. The latter two interfaces
are already public dependencies of retained imports.
The proof does not need `def-weil-pbc-strict-perfect-coefficient-package` or
`lem-weil-pbc-strict-perfect-ringed-pullback-model`: bounded site-flatness and the
published ordinary-extension K-flatness theorem suffice. The separately planned
stratum/slice restriction assembly is replaced by the existing normalized actual
`finiteFreeScalarRestriction` for the covering-scheme morphism.

The old characterization remains a public import because the original interface is
preserved; its theorem is not applied by the new proof. Its role in proof steps 1 and 7
is taken by the actual-ring criterion. No existing module is withdrawn, and no adopted
source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The assigned theorem uses fields in `Type (u + 1)` and their actual valuation rings.
`integralStratifiedPerfectCharacterization` and
`integralCompletedLocalPerfectCriterion` take fields in `Type u` and the lifted
`PbcIntegralRing`; their local models also use slice sites and a different stratification
presentation. They cannot be applied directly as the original DAG steps 1 and 7 propose.
The new criterion supplies precisely the actual-coefficient and covering-scheme interface
needed by those steps, without changing any target or coefficient definition.

The K-flatness proof fixes all three independent universes explicitly; leaving the
coefficient universe to inference generated underdetermined max-universe constraints.

## New nodes

`lem-weil-pbc-integral-padic-local-perfect-criterion`, in
`Sheaf.Paper.IntegralPadicLocalPerfectCriterion`, with its complete proof in words,
source, three Mathlib searches, and a Lean attachment. It is strictly a separate
one-coefficient characterization, not a renaming of scalar transport.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
