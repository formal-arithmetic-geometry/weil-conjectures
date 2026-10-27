## What changed

Proved `AlgebraicGeometry.ProEtale.integralSectionLocalIsomorphisms` with its
statement unchanged. The proof compares right adjoints under the existing section
equivalence and obtains the inverse-image comparison by uniqueness of left
adjoints. It then uses the existing algebraic pullback compositor and pro-etale
slice equivalence to compare local isomorphisms.

Added `Sheaf.Paper.IntegralSectionCoefficientNaturality`, containing the source
ring comparison and its compatible inverse-image coefficient isomorphism. This
is proved by lifting through the fully faithful forgetful functor to ring
sheaves and detecting invertibility after forgetting to abelian sheaves. Its
adjunction-unit calculation uses the filtered Kan extension and sheafification
comparison. All helpers are proved; no coefficient-normalization obligation is
postponed. Existing source-library files and shared definitions are untouched.

The item imports the canonical inverse-image adjunction, internal module
operations, slice comparison and strict pullback composition privately. Its two
original public imports are unchanged. Remote compilation in import order passed;
the final reduced import set was compiled as well. The original theorem signature
was checked byte for byte against the shared source.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralSectionLocalIsomorphisms`
(node `lem-sfb-integral-section-local-isomorphisms`).

Also proved the new ring-only theorem
`AlgebraicGeometry.ProEtale.integralSectionCoefficientNaturality`
(node `lem-sfb-integral-section-coefficient-naturality`).

Original holes: 1. Closed: 1. Added holes: 0. No `sorry` remains in either
delivered module. This is a proof, not a decomposition into new obligations.
Existing library dependencies are used with their existing axiom status.

## No longer needed

The planned direct dependency
`lem-c2-proetale-section-module-algebraic-inverse-image`
(`Sheaf.Paper.SectionModuleAlgebraicInverseImage`) is unnecessary for this proof:
the already proved direct-image comparison and uniqueness of left adjoints give
the required module inverse-image comparison. Its module is not imported by this
item. This is removal of a direct proof dependency, not a claim that the module
has no other consumers in the whole library.

No original public import was removed. No existing module or declaration is
withdrawn. The proposed finite-quotient normalization argument on the target is
unnecessary: the local-isomorphism statement only requires a compatible target
coefficient isomorphism, which the ring adjunction constructs uniquely.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no false statement was found. The previous proof
plan prescribed more comparison data than this isomorphism-class statement
needs. It is enough to compare right adjoints and construct a compatible target
ring isomorphism, rather than normalize a fixed detailed target comparison at
every finite quotient. The DAG proof and proof dependencies now follow this
shorter route. The blueprint unit route is preserved.

## New nodes

`lem-sfb-integral-section-coefficient-naturality` records the ring-only adjunct
coefficient square and its uniqueness, including the fully proved helper
construction `integralDetailedSectionRingComparison`. It is strictly about
coefficient rings and has no module or local-isomorphism conclusion. Both its
proof and the combining proof in the item module are complete. No split-off
`sorry` statements and no change records are added.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
