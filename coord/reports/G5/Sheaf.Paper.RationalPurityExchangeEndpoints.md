## What changed

Proved `WeilConjectures.RationalPurityExchangeEndpoints.rationalPurityExchangeEndpoints`
with the original theorem signature and every original named field type.
All original public imports are retained.
Added private, proved lemmas evaluating the specified composite comparison and deriving its
unit, tower, shift, inverse-purity, and whiskered-purity equations. Added a private proof that
packs `rationalScalarComparisonIdentification` into `LocalizedFamily`.

The domain argument uses the actual integral object retained by raw rationalization. For
pullback it applies the published object formula to that same representative and obtains
its uniform Tor interval from `rational_lattice_adic_domain`. Pullback geometry is obtained
from Mathlib's base-change stability. The normalized pullback comparison laws are taken
from the existing `TwistedPullbackCoefficientCoherence` theorem; only its `pu` and `pv`
coefficient and shift conclusions are used. The endpoint equations are then proved by
explicit naturality, cancellation, functoriality, and Mathlib's shift instances.

Added the private proof import `Sheaf.Paper.TwistedPullbackCoefficientCoherence`.
Updated the item's DAG proof and proof dependencies to match the Lean argument.
Moved the localized family into `Sheaf.Paper.RationalPurityLocalizedFamilyData`
and the remaining endpoint definitions into
`Sheaf.Paper.RationalPurityExchangeEndpointData`. Public imports preserve access
through the assigned module. No other existing module is changed.
`LocalizedFamily` now stores its five data fields and a proposition-valued record
containing exactly the original nineteen laws. All original named accessors retain
their parameter and result types. Its generated constructor and recursor
representation changes; no existing consumer uses those declarations.
Each complete law proposition is named transparently to cache its large inferred
instance arguments during record generation. The other thirteen moved definitions
retain their bodies. The two new definition nodes record these representations.
The original theorem signature, including its original unused binders, is retained
verbatim. The two unused-binder linters are scoped off for that declaration only.
No proof-checking or transparency option is weakened.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.RationalPurityExchangeEndpoints.rationalPurityExchangeEndpoints`
(node `lem-pur-rational-purity-exchange-endpoints`).
Added 0 holes; 0 holes remain in the delivered module. This proof uses the existing
stated dependencies, including `twistedPullbackCoefficientCoherence`; their remaining
proof obligations are not reintroduced or copied into this delivery.

The argument includes equal fields, empty schemes, relative dimension zero, arbitrary
integer shifts, torsion representatives, and arbitrary nonsmooth pullback maps. It retains
the specified counit mate, source normalization, coefficient units and associators.

Validation: import-ordered server compilation, a separate fieldwise representation
equivalence check against all nineteen literal original law types, source comparison
of all five data fields and twenty-four named accessor signatures, and the
delivery's compiler/axiom checks. The temporary representation-check module is not
part of the delivery. All three delivered library modules compiled cleanly in
the import-ordered server build, with the per-file limit enforced. The fieldwise
representation equivalence check also compiled.

## No longer needed

Removed the private import `Sheaf.Paper.IntegralOperationsPreserveConstructible`:
`constructibleIntegralPullback` already has constructible codomain, so its output's
property and the lattice-domain theorem suffice. Also removed the redundant private import `Mathlib.AlgebraicGeometry.Morphisms.Etale`;
its smoothness and base-change declarations are already public dependencies of
`RationalScalarComparisonData`. The integral-operations theorem remains
needed inside the construction of that published functor; no module is withdrawn.

Removed direct proof-dependency edges to `lem-pur-integral-operations-preserve-constructible`,
`lem-pur-adic-purity-scalar-naturality`, `prop-weil-pbc-scalar-extension`,
`thm-pur-rational-and-qbar-purity`, and `def-weil-pbc-rational-category`.
Their required constructions and normalization results are already encapsulated in the
retained declarations and public statement imports. This removes no required unit step.
The existing tool-use approvals are preserved. No claim is made that these modules
leave the targets' transitive import closure, and no adopted source declaration is changed.

## Where the brief, the DAG or earlier work was wrong

The old plan asks for another integral-model construction and localization argument.
For this module's already-published types, raw rationalization retains its integral
objects and the stated scalar-identification theorem supplies the entire normalized
localized family. Repeating those constructions is unnecessary. The existing
`lem-pur-twisted-pullback-coefficient-coherence` supplies precisely the ordinary
pullback coefficient laws needed for pasting. The mathematical statement is unchanged. The original mixed record generated
large declarations and spent 53 seconds in `.olean` serialization; merely
splitting the file did not meet the limit. Factoring its proof fields alone did not fix serialization. Naming their full
propositions reduced serialization from 77 to 47.5 seconds. The remaining
localized-family and endpoint parts are compiled as separate coherent modules.

## New nodes

`def-pur-rational-purity-exchange-endpoint-data`: the thirteen original endpoint
coordinate and domain definitions, with their original names, types and bodies.

`def-pur-rational-purity-localized-family-data`: the fieldwise-equivalent localized
family representation, its data/laws records and transparent law propositions.
Both nodes introduce definitions only, with no new mathematical assertion or proof hole.

Change record: `coord/changes/G5-rational-purity-endpoint-data-split.md`.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
