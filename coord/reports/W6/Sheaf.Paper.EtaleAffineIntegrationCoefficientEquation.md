## What changed

Proved `AlgebraicGeometry.Etale.AffineIntegrationCoefficient.equation` with its statement
unchanged. The bodies of `trace` and `unitIso` now share the irreducible
`ordinaryUnitIso`, which is exactly the original degree-zero unit isomorphism. This
removes repeated expensive monoidal-instance comparisons; the definitions remain
definitionally equal. See `coord/changes/etale-affine-coefficient-unit-cache.md`.
The common annihilator is obtained from
`Scheme.sf_bc_adic_ring_domain` and the inequality of each exponent with the maximum.
Specializing `affine_counit_scalar` to the ordinary coefficient unit supplies the
Noetherian base, invertible modulus, and the counit equation.

Private proved helpers identify the two equivalent constructibility conventions, transport
finite-Tor constructible objects along isomorphisms, verify the coefficient unit directly
by constant-sheaf stalk flatness, and transport the ambient adjoint to the library's exceptional adjoint. Existing small-etale
six-operation stability gives the compact-support, tensor-pullback, and ambient domains.
`etaleCtfChartDomain` and `etaleCtfChartScalarDomain` give site and scalar preservation.
The finite proper projection formula makes both actual projection maps invertible.
Naturality of the compactified counit along the normalized coefficient-unit isomorphism
proves the trace equation. The first part of `integrationTransposeScalarMate`, followed
by cancellation of the compact scalar isomorphism, gives the second equation.

The trace equation is proved once in a private lemma over arbitrary finite coefficient
rings, then specialized to the finite Tate stages. This avoids repeating concrete
coefficient-instance conversions. The complete diagnostic compiled in 31.5 seconds, and the actual module compiled
cleanly in 18.5 seconds through `lcompile.py`. All added imports are private proof imports. No
source-library files are changed.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.AffineIntegrationCoefficient.equation`
(node `lem-pur-etale-affine-integration-coefficient-equation`). Holes added: zero.
Holes left in the delivered module: zero. This proof uses existing stated dependencies;
it does not claim that their transitive axioms have all been eliminated.

## No longer needed

The proof does not need `lem-amb-affine-space-top-trace` or `def-amb-vector-integration`
as separate proof dependencies: the module already defines its trace to be the specified
compactified ordered counit. The imported `affine_counit_scalar` applies directly to it.
The tensor projection computation in Steps 4–5 is already proved by
`lem-pur-integration-transpose-scalar-mate`, so it is reused instead of repeated.
The private import `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace` is removed.
`thm-amb-vector-bundle-purity` is also removed from the proof dependencies: ordinary-etale
exceptional stability and uniqueness of right adjoints give the required domain, and the
finite proper projection theorem gives the actual projection isomorphisms. It remains a
statement dependency and public import. No modules are withdrawn. Existing public imports
and all unit realizations are preserved. The obsolete top-level tool approvals for
`thm-amb-vector-bundle-purity` and `lem-amb-affine-space-top-trace` are removed in order.
The private top-trace import remains transitively available through `AffineCounitScalar`;
this delivery does not claim that its module leaves the targets import closure.
The proof uses neither `sk-prop-sf-rf-shriek-preservation` nor `thm-sf-ctf-stability` as
a theorem dependency: their current attachments concern pro-etale categories. Instead it
uses the already proved small-etale source APIs named in the updated proof step.

## Where the brief, the DAG or earlier work was wrong

The DAG's domain argument can use the existing ordinary-etale exceptional-preservation
and tensor-stability theorems after explicitly comparing the two constructibility
predicates. This avoids translating general vector-bundle purity into the ordered affine
coordinates. The coefficient-map normalization is not definitional: the open comparison
isomorphisms agree by `compactScalarOpen_normalization`. This equality is included
explicitly in the Lean proof. Empty bases, dimension zero, and the zero coefficient ring
are retained by all the used statements; the common exponent is positive.
The source stability files contain no `sorry`; their names in the revised node are
explicit source-library reuse, not applications of the different pro-etale attachments.
No target statement, coefficient object or compactification definition is changed.
The trace and scalar-unit definitions retain the same maps through a shared irreducible
interface. Their signatures and all public imports are preserved.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
