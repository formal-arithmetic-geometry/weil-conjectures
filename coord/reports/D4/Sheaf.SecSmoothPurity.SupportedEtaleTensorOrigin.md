## What changed

Filled two of the three proof bodies in `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin`,
without changing public signatures or definitions. Added private categorical helpers for
balancing naturality, adjunction mates, and open/scalar comparisons. An instance-search
exclusion prevents an unrelated opposite-site monoidal instance from being searched. Imported the
supported constructible-origin theorem, intrinsic Tor-amplitude transport, and the source
open-shriek Tor-amplitude theorem.

The main theorem transports the intrinsic Tor interval to fixed coefficients, extends
it by zero, reflects it through etale comparison, and tests the resulting etale Tor
interval on the coefficient sheaf. The prescribed scalar/open arrow is invertible by
iterated adjunction mates. The original scalar/tensor existence-uniqueness statement remains unchanged
and unproved; its unique isomorphism is still used by the existing definitions.

## Proved and sorry left

Original holes: 3. Holes closed: 2. The final packet compiled without warnings or errors
in 32.5 seconds:

- `AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.proScalarSheafTensorMap_naturality`
- `AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.supported_etale_tensor_origin`

One original hole remains:
`AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.proScalarTensorIso_existsUnique`
(blueprint `lem-sp-supported-etale-tensor-origin`, already attached to this module).
Its public statement and complete K-flat normalization proof plan in its docstring are
unchanged. The delivery adds zero holes and splits off zero statements. This is a
partial-module proof delivery, not a claim that the module is axiom-clean.

I attempted to close the normalization theorem using the proved source-library
`leftDerivedSheafExtendScalarsProjection` and `leftDerivedTensorRightIso`. The missing
glue is the identification of the prescribed adjunction representative with the
canonical left-derived counit and of the Q tensorator with `derivedTensorSingleCounit`.
Generic adjunction and quotient-boundary calculations were developed in scratch work,
but the concrete specialization still triggered expensive localization/tensor
reduction. Those unvalidated attempts are not part of the delivered Lean module.

## No longer needed

`lem-sp-supported-scalar-tor-interval` and
`Sheaf.SecSmoothPurity.SupportedScalarTorInterval` are not needed by this proof:
the source-library Tor-interval transport and reflection theorems give boundedness
directly, and the scalar/open invertibility is proved by mates. This is pruning of this
item's proof dependency; no withdrawal of that module or its other consumers is claimed.

Removed these private imports:

- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`

Some were redundant through public transitive imports; the remaining planned proof modules are
unneeded by this argument. Existing public imports stay unchanged. The constructible
origin theorem remains a dependency and retains its own proof dependencies. No adopted
source declaration is removed, weakened, or replaced by `sorry`.

## Where the brief, the DAG or earlier work was wrong

The planned supported-scalar-Tor-interval dependency is stronger than needed for the
main Lean proof. The existing fixed-coefficient source API already preserves Tor
intervals under open extension and reflects them under site comparison. The node proof
and proof dependencies now record this route and the categorical mate argument.
No statement is disputed. There are no new nodes or forced adaptations.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
