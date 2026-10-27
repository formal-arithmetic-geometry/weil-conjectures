## What changed

Proved `supportedKummerReduction` by specializing the published Cartier family's
coefficient-reduction clause to the effective Cartier zero divisor. A proved private
helper specializes the predicate before substituting the large purity datum, avoiding
expansion during unification. All section-generator and derived scalar-unit equations
are retained.

The original `supportedProductsUnit` proof remains untouched. The attempted direct
empty-product proof encountered dependent equality transports in the existing
support/tower construction; no unverified proof of that clause is delivered.
No statement, definition, public import, or DAG route was changed. The direct
Cartier specialization covers a=b as well as a<b, arbitrary ramification and
nonreduced bases.

## Proved and sorry left

Closed 1 of the original 5 holes, with no new holes:

- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.supportedKummerReduction`.

The following four existing named theorem holes remain unchanged, all attached to
`lem-pur-finite-diagonal-orientation-reduction` with their original source and proof docstrings:

- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.affineOrientationReduction`.
- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.supportedProductsReduction`.
- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.supportedProductsUnit`.
- `WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction.diagonalOrientationReduction`.

The private helper is proved. This is a partial delivery of one existing clause,
not a decomposition: zero holes were added or split off. The imported Cartier,
Cartier normalization declarations remain the intended proof dependencies.

## No longer needed

Removed these redundant private imports (the interfaces used by the completed
proof are already public dependencies of the statement modules):

- `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction`.
- `Sheaf.Paper.SupportedCupFunctoriality`.
- `Sheaf.Paper.SupportedCup`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`.
- `Sheaf.Paper.FiniteAdjointMateCompatibility`.
- `Sheaf.Paper.FiniteCoefficientAdjointComparisons`.
- `Sheaf.Paper.VectorIntegrationSiteComparison`.
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`.

No node or module is withdrawn. The original DAG dependencies for the four untouched
proof holes remain needed; their future proofs still require the stated mate,
coefficient, cup-product and normalized diagonal arguments. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The Cartier reduction clause already includes
all scalar-unit and root-generator equations of `supportedKummerReductionAt`; no new
coefficient-compatibility lemma is necessary for that clause. The existing
zero-section purity theorem supplies the empty Thom inverse equation, but the
full empty-product clause also needs the canonical support-transport equality.
The affine exceptional adjunct, supported products and diagonal chain remain separate
work; this delivery does not claim to have supplied their geometric transport proofs.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
