## What changed

Filled the proof of `WeilConjectures.adicSmoothBaseChange`, preserving its signature,
its actual completed exchange, its finite-origin hypothesis and its complete
conditional constructible-landing clause. The input definition
`sbcAdicFiniteCohomology` and all public imports remain unchanged.

Finite invertibility is obtained from the stated finite pro-etale smooth-base-change
theorem, with the cardinality of the finite quotient as annihilator. Its fixed
scalar coordinate is related to the actual finite mate by the separate comparison
`WeilConjectures.sbcFiniteExchange_encoding`. The published reduction equation then
gives invertibility at every quotient. A proved private helper detects invertibility
using exact evaluation of the strict reduction tower and the naturality of its
completion unit. Another proved helper transports the common cohomological interval
and constructibility to the actual endpoint reductions and applies the existing
backward uniform reduction criterion. Full-subcategory reflection proves the final
isomorphism without changing the map.

Updated the item's proof route and added the separate finite-encoding module and node.
The new encoding module also contains fully proved private constant-section,
coefficient-adjunct, ordinary direct-image and normalized pullback Hom-comparison
lemmas. These discharge the ordinary comparison layer of its documented argument;
the public theorem still awaits derived compositor coherence.
There are no changes to existing definitions or statement signatures and no forced
adaptations. Only the sandbox is edited. All compilation is through lcompile.py. The corrected main module compiled cleanly in 13.2 seconds; the encoding module
with its proved private comparison layer compiled cleanly in 6.6 seconds, with no
warnings beyond its public theorem's declared hole. The first delivery command
returned DELIVERY BUSY after its queue wait; this packet retries that delivery.

## Proved and sorry left

Closed the one original body hole, `WeilConjectures.adicSmoothBaseChange`.
The assigned module has zero remaining sorries.

Added one hole, `WeilConjectures.sbcFiniteExchange_encoding`, in
`Sheaf.Paper.AdicFiniteExchangeEncoding`, attached to
`lem-sbc-adic-finite-exchange-encoding`. Its source and full argument are in its
docstring and node. It compares the actual maps before any geometric or boundedness
hypothesis; it asserts no smooth-base-change invertibility, completeness detection,
or constructible membership. Thus the packet is a decomposition, closing one upper
hole and adding one strictly separate lower hole, for net zero holes. The rest of the
combination is written Lean, with no anonymous or private holes and no data holes.

The proof uses existing project declarations, including those whose own proofs are
unfinished. This is not a claim that the full axiom closure is already sorry-free.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CompletedPullbackReduction`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.Paper.NormalizedEtaleOriginWitnesses`

The earlier explicit direct-image-limits, completed-pullback-reduction, perfect
projection formula and coefficient-restriction arguments are encapsulated by the
published `sbcReductionComparisons_isIso` and linear exchange identity. The previous
levelwise-cone route is replaced by exact strict-tower evaluation and the canonical
completion-unit square. The previous local-model/origin assembly is encapsulated by
`pbcUniformReductionCriterion_backward`. No unused dependency is imported merely to
keep the old plan alive.

Accordingly removed all the item's old top-level tool_uses approvals, in their
original order. Their ids are: prop-weil-pbc-direct-image-limits,
lemma-weil-pbc-completed-pullback-reduction, lemma-weil-pbc-perfect-projection-formula,
lem-weil-pbc-ring-sheaf-change-adjunction,
lem-weil-pbc-profinite-coefficient-inverse-image,
lem-weil-pbc-levelwise-isomorphism-cones,
lem-weil-pbc-constant-completion-equivalence,
lem-weil-pbc-normalized-constructible-local-effectivity,
lem-weil-pbc-finite-ring-constructible-derived-origin,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
prop-weil-pbc-site-comparison-finite-level, thm-weil-pbc-site-comparison, and
lem-weil-pbc-normalized-etale-origin-witnesses. They are no longer separate steps
of this proof. Some remain transitive dependencies of the existing interfaces;
this is not a request to delete those modules or any source-library declaration.
No module withdrawal is included.

## Where the brief, the DAG or earlier work was wrong

The finite theorem's docstring calls its realized fixed-scalar exchange the actual
ringed mate, but its Lean conclusion contains only realization applied to
`ProEtale.derivedBaseChangeMap`. It does not mention `sbcFiniteExchangeApp` or the
normalized tensor pullback square. Hence one cannot directly apply it to the
finite map occurring in the completed reduction equation. The new encoding result
records this genuine presentation comparison. The existing
`proEtaleConstantExchange_encoding` has a small coefficient type with an ULift
constant-ring presentation and restriction in the opposite direction; it does not
specialize in one line to these quotient function coefficients and the canonical
`pbcDerivedFunctionRealization`. The proper finite exchange transport theorem has a
properness hypothesis and cannot supply smooth exchange here.

The uniform reduction criterion already assembles the old plan's local models and
compatible origins. Repeating that assembly would add no mathematical content.
The square orientation, finite dimensions and four finite-output interval hypotheses
are retained exactly. Empty schemes and zero quotient rings cause no problem in the
encoding lemma; the quotient ring still has a positive cardinality.

The unit `sk-rem-rest` has no additional realized statement/step list that this route
bypasses. The finite smooth theorem remains a dependency.

## New nodes

`lem-sbc-adic-finite-exchange-encoding` is the separate presentation comparison in
finite smooth base change: the actual quotient ringed mate is isomorphic as an
arrow to fixed-scalar exchange under the canonical derived function realization.
It is independent of smoothness, boundedness, noetherianity, completion and etale
origin. Its proof is the constant-section direct-image comparison, normalized
adjunction/compositor transport, and the unit-square-counit identity. The new
module has one public statement with exactly this source argument, the node has
the verbatim Lean signature, and all three search styles are recorded. No change
record is required because no existing statement or definition is changed.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
