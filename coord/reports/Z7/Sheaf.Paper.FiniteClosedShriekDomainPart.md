## What changed

Proved `WeilConjectures.finiteClosedShriek_domainPart` with its unchanged signature.
A proved private helper transports the existing upstream exceptional-preservation
result into the intrinsic finite-Tor predicate. Scalar preservation is the membership
component of `closedScalarDomains_scalar`; conjugating by `ULift.ringEquiv` handles
the lifted input homomorphism exactly. The three conclusions are assembled from
scalar preservation, exceptional preservation over E, and exceptional preservation over L.
No new public declaration, definition, attribute, or public import is introduced.

Added proof imports of `Sheaf.Paper.ClosedScalarDomains` and
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness`.
Updated the item's proof plan and proof dependencies to this argument.
The module compiled without warnings in 8.0 seconds through lcompile.py.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.finiteClosedShriek_domainPart`
(node `lem-coef-closed-shriek-domain-part`). Added 0 holes. No sorry remains in the item.
The private helper `splitExceptionalDomain_preserves` is fully proved.
No new sorried or public helper statements are introduced.

## No longer needed

Removed the unused proof import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor`.
This item's proof no longer needs the planned dependencies
`lem-coef-closed-transpose-cocycles`, `lem-coef-finite-direct-image`,
`prop-sf-closed-unit-all-stages`, or `prop-sf-localization-all-stages`.
Their map, adjunction-unit, and localization-coherence conclusions are unnecessary
for these three membership assertions. Public imports are retained to preserve
all existing consumers' environments; no existing module is withdrawn.
The scalar-domain dependency remains used. Unit routes and upstream declarations stay intact.

## Where the brief, the DAG or earlier work was wrong

The original plan mixed the geometric membership assertions with the separate
transpose and invertibility argument. Existing scalar-domain preservation and
upstream `ProEtale.constructibleFiniteTor_rightDerivedUpperShriek` already give
all the necessary mathematics. The latter has precisely the same comparison-site
functor as `sfFiniteExceptionalFixed`, so no comparison isomorphism must be assumed.
The output fixed-module Tor predicate does not require ordered endpoints; widening
to `[min c d,d]` makes its transport to the intrinsic ordered predicate valid,
including for zero objects and empty schemes. No statement repair was needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteClosedShriekDomainPart": "57c24204c246e816ec7b8dbf68f494d96dc915d4"}, "results": {"Sheaf.Paper.FiniteClosedShriek": {"hash": "8ba36df52168445c9b28d7eed8c9dd513f74aab8", "status": "OK"}}, "seconds": 93, "time": "2026-10-28T15:54:39+0800", "transitive": 0, "version": 1}
```

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
