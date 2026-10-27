## What changed

Filled the auxiliary proofs `coherence`, `tensor_domain`, `exchange_isIso`,
`projection_isIso`, and `mapSeparated` in
`Sheaf.Paper.RelativeProductBaseChangeFactorSquares`. The coherence proof selects
fields of the supplied datum. Finite tensor closure transports Tor intervals to
fixed-module coordinates, adds their endpoints, and transports the result back;
integral tensor closure uses the integral residue-Tor predicate equality. Exchange
invertibility follows from the corresponding datum axioms through
the explicit conjugating isomorphisms and full inclusions. Finite projection
invertibility applies the existing `compactSupportProjectionFormula` law directly;
the higher-stage projection cases use datum axioms. Separatedness follows
from the separated structure map.

Added proof imports for `IntrinsicTorAmplitudeTransport`, `IntegralResidueTor`,
`CompactSupportProjectionFormula`, and the existing source-library
`DerivedCategory.FlatModel`, and a proved private isomorphism-invariance helper for intrinsic Tor amplitude. Updated the existing
node's proof and proof dependencies to record these auxiliary arguments. Existing
public declaration signatures, definitions, public imports, and the six-factor
unit route are unchanged. Comparison isomorphisms and residue fields are marked
locally irreducible during proof elaboration; this changes no exported attribute
or definition. Geometric finite-type and quasi-compactness instances are derived
from the structure morphisms when applying the projection law.

## Proved and sorry left

Closed five of the six original holes:

- `WeilConjectures.RelativeProductBaseChange.coherence`
- `WeilConjectures.RelativeProductBaseChange.tensor_domain`
- `WeilConjectures.RelativeProductBaseChange.exchange_isIso`
- `WeilConjectures.RelativeProductBaseChange.projection_isIso`
- `WeilConjectures.RelativeProductBaseChange.mapSeparated`

One original hole remains:
`WeilConjectures.RelativeProductBaseChange.factor_squares`, node
`lem-sf-relative-product-base-change-factor-squares`. Its original independent
beta definitions, statement, and complete natural-language proof are retained.
No holes were added or split off. The private Tor-amplitude helper is proved.

Validation: the complete item compiled without errors or warnings through
`lcompile.py` in 58.6 seconds. All six original theorem signatures and all
30 existing definition bodies were compared with the repository and are unchanged.

## No longer needed

Removed the unused private imports `Sheaf.Paper.ExchangeFunctoriality`,
`Sheaf.Paper.IntegralCoherenceTower`, and
`Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`. Their nodes are retained
in the original proof plan of the remaining factor-square theorem; this delivery
does not claim those results are mathematically unnecessary. No module or node
is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No disputed statement was found. The original node did not list the Tor-amplitude
transport and integral residue-Tor lemmas used to prove its auxiliary domain
checks; these and the finite projection-formula dependency are now recorded. The
finite tensor proof does not assume that an
arbitrary `SixFunctorSpace` is separated over the base: it works directly in the
fixed-module derived category. No new statement or definition repair is needed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
