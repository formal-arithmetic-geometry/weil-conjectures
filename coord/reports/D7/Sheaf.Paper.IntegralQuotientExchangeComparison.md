## What changed

Prove `AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_exchange_comparison`
by specializing the existing proved generic `scalar_geometric_exchange_rectangle` to
`reduction l E n`. The ambient exchange is definitionally that theorem's exchange.
The private `normalized_inverse` calculation identifies all normalized pullback
comparisons, transporting the direct-image theorem's invertibility to the supplied b.

Use one simultaneous normalized scalar section family. Its actual scalar pairs,
ordinary and derived comparisons satisfy exactly ScalarRealized. The generic
rectangle's proved realization calculations give both ExchangeRealized clauses,
the balancing realization, and the specified projection mate realization. Transport
the internal rectangle for this same family, extend it through the essentially
surjective section equivalence, and cancel direct image of chi_h to obtain the last
natural-transformation equality on the entire section-derived category.

Existing visibility and all arguments stay unchanged. The main theorem's final
existential is now named SectionExchangeRealized before specialization. The ambient,
pull/push section and exchange wrappers reuse the existing generic constructions;
ExchangeRealized writes the equivalent equality with sides reversed. The scalar
predicate and the full section existential are factored over a general coefficient
map before specializing to the quotient. These expression-size repairs retain
the actual maps and equations.

The generic rectangle is a public import because these wrappers use its API.
Private imports reuse its proved realization calculations, normalized_inverse,
and the simultaneous normalized section family. The downstream.py scan found
zero Lean consumers of this module, including a --uses scan of every modified
wrapper. No source-library declaration is edited.

Change records:

- coord/changes/integral-quotient-exchange-canonical-wrappers.md
- coord/changes/D7-integral-scalar-realization-predicate.md
- coord/changes/D7-integral-section-realization-predicate.md
- coord/changes/D7-integral-quotient-exchange-proof-context.md

The item's proof, proof_deps and proof_origin follow the specialization. Its
obsolete tool_uses entries are withdrawn. No other module or node is edited.

Reviewer correction (cc review, 2026-10-25): ambient and sectionExchange no longer
reuse the theorem-module definitions scalarAmbientExchange and sectionRectangleExchange;
their bodies are the same mates written with the owned adj/scalarPullbackSquare and
sectionSquare (sectionExchange is back to its original body). ExchangeRealized is stated
on this module's wrappers ambient, pushSection, pullSection, sectionExchange. The item's
stmt_deps now cite the owners def-sfb-internal-derived-scalar-comparisons,
def-sfb-scalar-pullback-square-data,
def-sfb-internal-section-scalar-pullback-comparison-data and
def-sfb-scalar-section-push-comparison-data. The module compiles (lcompile 28.1 s).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.IntegralQuotient.integral_quotient_exchange_comparison`
(node `lem-sfb-integral-quotient-exchange-comparison`).

Sorry left in delivered modules: none. Added holes: none. Split off: none.
This is a proof from existing library declarations, including their existing
normalization dependencies; it introduces no assumptions or new holed statements.

Validation: lcompile.py compiled the full delivered module in 19.6 seconds
(exit 0). Its categorical helper diagnostic also compiled, checking the general
internal rectangle in 0.605 seconds in the kernel. The full compile uses the
ordinary limits, no profiler and no increased heartbeat limit. The initial
required delivery run confirmed the prior disk failure was resolved and exposed
the kernel conversion problem repaired here. deliver3.py performs the final
preflight and axiom checks before pushing.

## No longer needed

Removed private imports:

- Sheaf.CategoryTheory.ExchangeMateCube
- Sheaf.Paper.FiniteReductionExchangeRectangle
- Sheaf.Paper.IntegralFinitePullbackComposition
- Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.FourArrows
- Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.CategoryTheory.InternalSectionTensorComparison
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

The parent proof does not use the planned
`lem-sfb-integral-quotient-pullback-face-model`
(Sheaf.Paper.IntegralQuotientPullbackFaceModel) or
`lem-sfb-integral-quotient-section-mate-realization`
(Sheaf.Paper.IntegralQuotientSectionMateRealization): the already-proved generic
scalar exchange rectangle supplies the normalized internal equality and the precise
section realization calculations. It therefore does not require the planned direct
applications of `lem-weil-pbc-exchange-mate-cube`,
`lem-weil-pbc-intrinsic-finite-exchange-rectangle`, or `def-weil-pbc-four-arrows`.
The section rectangle here is established directly for the actual scalar pairs and
actual section adjunctions, rather than via a properness-specific four-arrow datum.

Withdraw all former item tool_uses entries:
`det-prop-sfb-qlbar-colimit-x-integral-limit`, `lem-pc-kflat-resolution`,
`lem-pd-section-derived-pushpull-normalization`,
`lem-pe-internal-section-tensor-comparison`, `lem-pur-derived-change-of-rings`,
`lem-sfb-internal-section-scalar-adjunction`, `lem-weil-pbc-exchange-mate-cube`,
`lem-weil-pbc-intrinsic-finite-exchange-rectangle`,
`lem-weil-pbc-proetale-derived-pullback-composition`,
`lem-weil-pbc-profinite-coefficient-inverse-image`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
The existing generic rectangle and direct-image theorem encapsulate their required
normalizations; the parent does not instantiate these auxiliary results directly.
The geometric normalization remains a proof dependency because the generic
module's private exchange realization calculations explicitly use it.

These are dependency removals from this parent's route only. No source-library
module or declaration is removed, and no globally unused-module claim is made.
The unit's own statement and realized proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction. The named irreducible section predicate
is a definitional presentation of the unchanged final existential; the main
signature's presentation changes for the expression-size repair described in
D7-integral-section-realization-predicate.md. The existing planned route predated the
proved generic scalar/geometric exchange rectangle and repeated its normalization
work. Library search found that shorter route. The stronger section assertion is
retained: equality on the image of the section equivalence is extended to every
section-derived object using naturality and essential surjectivity.

The retained attempt elaborated but timed out in kernel checking. The scalar
realization predicate repeated its full generator and K-flat equations after
specialization to completed coefficient rings. Factoring the same predicate and the complete existential over
an arbitrary map avoids this expanded conversion; the geometric wrappers likewise
reuse the generic definitions. Proved helpers over abstract categories assemble
componentwise route equality into natural-transformation equality and cancel the
inverse edge before specializing the derived-category functors. No file is split and the time limit is unchanged.

Searches run through msearch.py: LeanFinder for scalar extension/base-change mates
(two formulations), Loogle for mateEquiv composition, and grep for exchange/scalar
or reduction combinations. Mathlib results are generic mate identities or ordinary
module scalar extension; rg of the project found the applicable proved generic
rectangle and its normalized section family. The source read is
literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.proof.md,
paragraph (3). The argument works for quotient exponent one (n=0), nonflat
coefficient projection, identity squares, empty schemes, and zero complexes;
no boundedness, properness or completeness hypothesis is introduced.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
