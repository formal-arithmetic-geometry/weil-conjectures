## What changed

In `Sheaf.SecSmoothPurity.ReductionCompatibilities`, proved
`AlgebraicGeometry.ProEtale.reductionCompatibilities_unit` and
`AlgebraicGeometry.ProEtale.reductionCompatibilities_composition` with their exact existing
signatures. Two proved private categorical helpers perform the counit-transpose calculations.
The application lifts the canonical support comparisons and scalar associators to the full
Dctf subcategories, uses `reductionDirectImage_isIso` for cancellation and
`reductionDirectImage_cocycle` for the composition equation, and then takes underlying arrows.
The prime-power cardinality in the finite-field datum supplies characteristic p; boundedness
supplies a finite interval containing all nonzero cohomology degrees.

Updated Steps 2 and 3 of `det-sp-reduction-compatibilities` to record these calculations.
The unit route and the remaining purity plan are retained. No public declaration, definition,
or public import was changed. No other module was adapted.

Searches: LeanFinder for adjunction mates with unit/composition found Mathlib's
`unit_mateEquiv` and `mateEquiv_vcomp`; Loogle for `Adjunction.homEquiv` reported an unknown
unqualified identifier; grep found the adjunction Hom-equivalence and mates API. Direct
source inspection confirmed that counit transposition and epic cancellation are sufficient
and avoid constructing inverse natural isomorphisms on full subcategories.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.reductionCompatibilities_unit`.
- `AlgebraicGeometry.ProEtale.reductionCompatibilities_composition`.

Left 1 original hole, unchanged:

- `AlgebraicGeometry.ProEtale.reductionCompatibilities_purity`
  (`det-sp-reduction-compatibilities`, Steps 1 and 4--8).

Added 0 holes and split off 0 statements. The two private helpers are proved.
This is a partial delivery of the multi-theorem module, with two genuine hole closures.
The purity statement and its detailed natural-language proof remain available for the next
worker; its projection/scalar square and normalized orientation comparison have not been
formalized by this delivery.

## No longer needed

Removed these unused private proof imports from the item:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.
- `Sheaf.Paper.FiniteRingCompactSupportProjection`.

The two completed clauses use only the already public scalar, compact-support, and full
subcategory interfaces. No node or module is withdrawn or claimed globally unnecessary:
the listed tensor/projection dependencies remain in the DAG plan for the unchanged purity
hole. In particular `det-sp-finite-general-ring` and the exceptional comparison interface
remain required in the statements, and all public imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The categorical calculations work directly with the
multiplicative counit equations already present in the signatures; no explicit inverse
support arrow is needed. The compactification factorization is `cpt.comm.symm`.
The purity clause requires its separate tensor and orientation work; the completed unit
and composition calculations alone do not prove it.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
