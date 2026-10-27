## What changed

Closed thirteen of the fifteen original holes using the published finite pro-etale,
completed, finite-extension and common-stage compact-support theorems. Witness
transport retains the actual canonical maps and origin; the integral clauses retain
intrinsic completeness and compatible reductions; the rational and common-stage
clauses retain their uniform landing and normalization data. The geometry helpers
use the actual finite-type structure maps.

Added private proof imports for witness-map normalization, completion-presentation
transport and finite-type dimension. Updated the node proof route. All existing
signatures, definition bodies, docstrings and public imports are preserved. Local
irreducibility controls prevent expansion of derived category models while checking
the common-stage formulas. No other module is changed.

## Proved and sorry left

Closed 13 of 15 original holes, by declaration name:
`WeilConjectures.sfCompactSupportDomain_finiteProetale`,
`WeilConjectures.sfCompactSupportDomain_witness`,
`WeilConjectures.sfCompactSupportDomain_witness_identification`,
`WeilConjectures.sfDomainIntegralComplete`,
`WeilConjectures.sfCompactSupportDomain_integral`,
`WeilConjectures.sfCompactSupportDomain_integralRefinement`,
`WeilConjectures.sfDomainNoetherian`, `WeilConjectures.sfDomainGeometry`,
`WeilConjectures.sfCompactSupportDomain_rational`,
`WeilConjectures.sfCompactSupportDomain_rationalRefinement`,
`WeilConjectures.sfDomainDimension`, `WeilConjectures.sfDomainInvertible`, and
`WeilConjectures.sfCompactSupportDomain_qbar`.

Two original holes remain: `WeilConjectures.sfCompactSupportDomain_finite` and
`WeilConjectures.sfCompactSupportDomain_qbarRefinement`. Both retain their complete
original statements, proof docstrings and node `lem-sf-bc-compact-support-domain`.
Added holes: zero. Split-off statements: zero. This is a partial proof delivery.
The finite proof still needs efficient normalization between formalism components
and the concrete derived functors. The final refinement needs coherent localized
comparison families normalized on integral lattices, followed by descent.

## No longer needed

Removed private imports:
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`,
`Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`,
`Sheaf.Paper.PbcRationalTransport`, `Sheaf.Paper.PbcDescentFunctors`,
`Sheaf.Paper.PurityFiniteSettingComparisonHypotheses`,
`Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`, and
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`.
The geometry proof imports `PurityFiniteSetting` directly. Existing public compact-
support imports already supply the proof APIs that remain necessary.

The integral completeness proof uses the existing presentation lemma from
`PbcCompletedPullbackActual`; it does not require `WeilTensorProduct` or node
`def-wf-tensor-product`. Rational refinement follows by applying the actual
rational-arrow operation to the completed equation, without a separate rational
transport theorem. The open common-stage refinement still retains the planned
rational-transport and descent dependencies. No module is withdrawn, no source-
library declaration is removed, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

Witness transport identifies the source-library compact-support exchange; matching
the separately named canonical finite-coefficient map additionally uses the
normalized ordinary-open comparison. The common-stage theorem contains an extra
componentwise invertibility clause; the assembly retains every requested clause
and discards only that redundant clause.

The earlier disk-full compiler failure no longer occurs. Expanding the finite
formalism inside its component proof caused repeated elaboration or kernel-checking
timeouts. That proof is therefore left as its original named hole. Local controls
on the derived and localized category instances resolved the corresponding
common-stage signature cost without changing its formula.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
