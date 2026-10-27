## Worker report

Q76 states `lem-sf-finite-exceptional-site-normalization` in
`Sheaf.Paper.FiniteExceptionalSiteNormalization`. No proof is supplied: the three
assertions end in `by sorry`; every definition has actual data. The helper records
collect exactly the normalization data asserted by this node, rather than imposing
normalization hypotheses on the finite theorem. The H2 repair below adds five definition-node ownership records for already existing canonical maps.

The statement is recorded in three declarations. `finiteExceptionalSiteNormalization`
provides the finite data and quotient equation. `integralExceptionalSiteNormalizationAt`
is the conditional integral implication for an individual input.
`integralExceptionalSiteNormalization` gives the natural version when the hypotheses
hold on the entire integral constructible domain. This additional natural version
does not replace the objectwise implication.

Hypotheses and coefficient conventions:

- `D : FiniteFieldDatum`, `hl : l ≠ D.p`, and `[Fact l.Prime]` are the fixed algebraic
  closure of the finite field and the invertible prime. `E`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]` give the finite
  coefficient extension. `A l E n` is the existing quotient at exponent `n+1`, lifted
  to the sheaf-value universe. Its ideal uses the recorded chosen uniformizer.
- `[X.Over (Spec (.of D.k))]`, separation, local finite type, and quasi-compactness
  of its structure morphism render the separated finite-type hypothesis. The integral
  construction also displays the induced finite-type structure on Z and the `IsOver`
  certificate for i, which are consequences of the closed immersion, not independent
  geometric restrictions. The finite theorem does not require those certificates.
- `i`, `[IsClosedImmersion i]`, `j`, `[IsOpenImmersion j]`, and
  `IsCompl (Set.range i) (Set.range j)` give the closed/open decomposition. The
  quasi-compactness of j follows in this Noetherian setting and is displayed because
  the published closed-kernel interface requires it.
- `C`, `bc`, and `red` use the original small pro-etale site, the published intrinsic
  constructibility predicate, and the canonical intrinsic realization equivalence.
  There is no finite-Tor condition. Integral categories use exactly
  `sfIntegralConstructible`, including intrinsic completeness and a single uniform
  cohomological interval for all positive reductions.
- `J`, `a` and `JR`, `aR` are adjunction presentations of the closed-kernel right
  adjoints over the actual closed direct images. The theorem is universal in those
  presentations, and therefore applies to the kernel right adjoints and their
  normalized counits supplied by `proEtale_ringed_closed_kernel_adjoint`. It does not
  posit an arbitrary map in place of any canonical construction. Uniqueness of
  counit-compatible right adjoints removes dependence on the presentation.

Finite clauses:

- `etaleSupport` is the ordinary etale compact-support functor at
  `Compactification.ofIsProper i`, whose open part is the identity. Its ordinary
  right adjoint is `etaleExceptional`. `FiniteNormalization.etale_preserves` is
  bounded constructible preservation, and `etale_triangle` uses its actual counit
  and the actual etale open adjunction unit.
- `exceptional` is literally the recorded `sfFiniteExceptionalAt`: Rnu_X,* followed
  by this etale right adjoint followed by exact nu_Z^*. `comparison` is a natural
  isomorphism on the full bounded constructible category, with no chosen origin as
  a parameter. `kernel_preserves` records constructibility of its first side.
- `counit` is the canonical pro-etale exact-termwise comparison followed by
  `ClosedFiniteTransport.transportedCounit`; that latter map explicitly contains
  the closed site-comparison inverse, etale exceptional counit, and comparison
  counit. `counit_eq` identifies it with the kernel counit.
- `boundary` and `distinguished` give the actual supported triangle with kernel
  counit and `openUnit`. `triangle_unique` compares it with every distinguished
  triangle using the specified exceptional counit and open unit. Its uniqueness
  fixes ONLY the middle and open components; the required closed component is
  separately identified with the comparison. Thus it applies in particular to
  the pulled-back triangle of every bounded constructible etale origin.
- `unit_unique` gives the exceptional unit as the unique counit transpose of the
  identity on a constructible closed image. `specifiedShift` uses the canonical
  adjunction shift on the etale right adjoint and the existing shifts on the site
  functors; `shifts` is its compatibility square with the kernel adjunction shift.
- `quotient` is the quotient induced by the identity on the valuation ring, and
  `scalar` is the published actual derived scalar extension. `Quotients.projection`
  is fixed, component by component, to `finiteCoefficientChangeDirectImageMap`.
  `quotientMate` is its inverse mate under the two kernel adjunctions, hence exactly
  the coefficient-extended exceptional-counit transpose.
- `etaleProjection_eq` fixes the ordinary etale compact-support scalar map;
  `compatible` identifies its `etaleCoefficientQuotientMate` with `quotientMate`
  under the two site isomorphisms. `origin` is the image of the actual comparison
  adjunction unit, and `origins` states its invertibility. The equation is in the
  smaller coefficient category. It ranges over all bounded constructible etale
  origins whose reduction is bounded constructible; every input in the node has
  such an origin by the recorded finite-ring derived-origin theorem. Naturality
  transports the equation along any origin isomorphism. There is no coefficient
  flatness or finite-Tor hypothesis. Identity and composite quotient maps are the
  existing canonical quotient/adjunction maps, rather than chosen isomorphisms.

Integral clauses:

- `closedCompactIso` uses the actual forget-supports map at any closed
  compactification, followed by the derived direct-image compositor. It lets
  `integralEvaluation` compare the specified chosen compactification with `(id,i)`
  by an ordinary counit mate, with no arbitrary compactification identification.
- `integralEvaluation` evaluates the ACTUAL `integralExceptionalSystem`. Its
  factors are the coordinate equivalence counits, normalized site direct/inverse
  comparisons, the ordinary system adjoint evaluation, and the etale right-adjoint
  mate. This retains finite coefficient actions and the specified tower.
- `closedReduction` is the recorded scalar-unit-normalized completed direct-image
  reduction map, transported through the canonical fixed/intrinsic equivalences.
  `he` is precisely reduction of the original integral counit. `e` is the finite
  comparison after composing the assumed kernel reduction with the finite site
  normalization; it is therefore an isomorphism to the specified finite functor.
- `integralLevelAt` and `integralLevel` are the level maps of this normalization.
  `hc` expresses compatibility with the ACTUAL quotient transitions, in the
  larger finite coefficient category via `normalizedDVRRes`. It does not forget
  the finite action or assume a lift exists.
- The conclusion first produces `b`, an isomorphism in the ordinary derived
  category of strict coefficient systems, before evaluation or scalar forgetting.
  Its evaluation equation fixes the stated normalized finite maps. The proof
  docstring constructs b by the ordinary system adjunction; it never invokes
  fullness or faithfulness of evaluation to construct it.
- `gamma` has the literal specified `integralExceptionalInverseImage` as its
  target, which is the actual total derived limit of the scalar-restricted system.
  Its displayed formula is the actual reduction/limit unit followed by the limit
  of b. `targetReduction` is the genuine reduction/limit counit followed by the
  canonical evaluation map. The `gamma` equation with `targetReduction` identifies
  its reductions with e, rather than merely asserting some limit isomorphism.
- The natural theorem also supplies the induced exceptional counit `epsilon`,
  identifies it after the direct image of gamma with `aR.counit`, and states the
  corresponding unit triangle equation. Both integral forms explicitly require the
  induced counit to reduce to the specified finite exceptional counit after the
  actual closed direct-image comparison and target reduction. Thus this counit
  is normalized independently of the mere existence of gamma. The objectwise theorem asks only that
  K and JR(K) be integral constructible, exactly as in the node.

Dependency declarations used (their modules are imported):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the coefficient constructions from
  `CoefficientExtension`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its category.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`:
  `Scheme.sfIntrinsicCompactSupport` (same compact-support convention).
- `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`:
  `Scheme.ringedClosedKernelShriek`, `proEtale_ringed_closed_kernel_adjoint`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public
  `FixedFiniteExceptionalAt`: the recorded exceptional definition and
  `ProEtale.sfFiniteExceptionalAt`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and
  `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`: the recorded completed
  coefficient sheaves, canonical comparison, and projections.
- `Sheaf.Paper.ClosedFiniteAdjointCounitTransport`:
  `ClosedFiniteTransport.compactSupportIso`, `transportedCounit`, `proTermwise`.
- `Sheaf.Paper.FiniteCoefficientDirectImage`:
  `ProEtale.finiteCoefficientChangeDirectImageMap`.
- `Sheaf.Paper.WitnessCompatibility`: `pbcFixedScalarExtension`,
  `pbcComparisonReduction`.
- `Sheaf.Paper.EtaleSystemQuotientNormalization`:
  `Etale.etaleCoefficientQuotientMate`, with the canonical `compactScalarMap`.
- `Sheaf.Paper.IntegralExceptionalInverseImage`: `integralExceptionalSystem`,
  `integralExceptionalInverseImage`, `integralExceptionalSupport`,
  `integralExceptionalAdjoint`, and the canonical system coordinates.
- `Sheaf.Paper.ExceptionalDerivedSiteRealization`,
  `ExceptionalFiniteSupportRealization`, and `ExceptionalProEtaleRealization`:
  `integralExceptionalSiteDerivedRight`, `integralExceptionalSiteDerivedInverse`,
  `integralExceptionalEtaleRightAdjoint`, and coordinate evaluation comparisons.
- `Sheaf.Paper.SfExceptionalReductionTransitions`: `directReduction`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedDirectImageComparison`, with the intrinsic equivalences.
- `Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction`: the simultaneous
  strict-system reduction used in the integral proof plan. This is a proof-only
  dependency. The unused `Sheaf.Paper.IntegralStrictReductionModel` import was
  removed in the H7 repair below.
- Mathlib `mateEquiv`, `Adjunction.ofNatIsoLeft`,
  `Adjunction.RightAdjointCommShift.iso`, and `Triangle` are reused directly.

The statement dependencies use existing landed definitions. The H2 repair adds five
existing:true definition-node ownership records for canonical maps previously cited
through theorem nodes. No dependency module or duplicate Lean declaration is added.
Proof-only imports supply the nodes used in the complete docstring proof plans.

Edge cases checked: all positive exponents are covered by n+1 (including exponent
one); equal-level quotient is induced by the identity; nonflat proper quotients
carry no flatness constraint; the empty scheme and zero complexes require no
nonemptiness or positive-dimension hypothesis; empty/full closed loci satisfy the
same complement predicate; shifts range over all integers; bounded constructibility
is not replaced by finite-Tor constructibility; the integral implication does not
assume finite-level maps lift by a faithful evaluation functor.

Searches: prescribed msearch.py LeanFinder query for the full closed-kernel/site/
quotient/integral normalization returned eight unrelated kerAdjunction/normalization
hits; Loogle `CategoryTheory.Adjunction.rightAdjointUniq` returned twelve generic
uniqueness/unit/counit lemmas; Mathlib grep
`ringedClosedKernelShriek|exceptional.*counit` in CategoryTheory returned zero;
LeanSearch for closed-immersion exceptional inverse image etale/proetale kernel
comparison returned eight generic closed-immersion facts. The exact results are in
`sandbox/searches.jsonl`. Searches by item ID in WeilConjectures and Sheaf returned
no declaration for this node. Broader rg searches found and reused the finite
counit transport, quotient mates, strict reduction, and integral exceptional system
modules above; none states this combined assertion. No statement correction or
STATEMENT-DISPUTED issue was found.

## Second reading by Q76

Self-audit against the node and current blueprint, under the dispatcher's explicit
instruction not to start other agents. The maintainer performs the independent
review after delivery; no independent worker review is claimed here.

Fixed during this reading: use pro-etale rather than etale termwise closed
comparison in the transported counit; use the actual left-derived open unit;
make triangle uniqueness fix only middle/open components; expose the etale
supported triangle and shift/unit clauses; replace the initial finite-only
existence with the quotient-normalized data; construct an explicit evaluation of
the specified strict integral system and its actual target reduction; provide the
objectwise integral implication so that a global preservation hypothesis does not
replace the node's objectwise premise. All helper data are canonical constructions.


Repair self-reading: opened all five existing source definitions and their new
node records side by side. The closed transport record gives lambda inverse, then
the transported etale counit, then the comparison counit in the actual code order;
its finite-ring and complement hypotheses match the section parameters. The
quotient-mate record gives precisely mateEquiv applied to q.inv under the two
specified adjunctions. The coefficient direct-image record characterizes the
same uniquely determined B-linear counit transpose chosen by the implementation,
without importing its separate isomorphism assertion. The integral direct-reduction
record has the same scalar-adjunction transpose, reduction unit and restriction
comparison as directReduction. The compact-scalar record packages exactly the
existing proper/open component map, with no duplicate components. Verified each
new statement's bracket citations equal its stmt_deps and that no new dependency
path reaches this item. All five are existing:true records: neither helper code
nor a new postponed theorem is introduced. The original empty-scheme, exponent-one,
equal-level quotient and independent-universe edge cases therefore still apply.


## Returned-head repair

Repaired the maintainer's H2 return of immutable head `526c54e51b4e`.
Compared the retained sandbox node with the current shared node: the latter has the
original ten statement dependencies and no Lean record. The mathematics, all 28
local declarations, all three theorem signatures, and every proof docstring remain
as in the independently checked returned delivery.

The four added theorem dependencies used only for definitions are replaced by
`def-sf-closed-finite-counit-transport`,
`def-sf-etale-exceptional-quotient-mate`,
`def-sf-finite-coefficient-direct-image-map`, and
`def-sf-integral-direct-reduction-map`. Their existing:true Lean records point at
exactly the landed canonical definitions, with their actual signatures. The fifth
new dependency, `def-sf-etale-compact-scalar-map`, explicitly owns and cites
`AlgebraicGeometry.Etale.compactScalarMap`; its module is now a public import.
No new theorem assertion or copied implementation supplies any of this data.

`lem-sf-closed-direct-image-strict-reduction` and
`def-sf-integral-strict-reduction-model` have been removed from stmt_deps.
The former remains in the original proof_deps and is an ordinary, non-public
import. The H7 repair below restores proof_deps to the original 32 entries and
removes the unused integral strict-reduction-model import. The coefficient-direct-image
and exceptional-reduction maps remain available through their definition-node
owners and public imports. The other returned theorem nodes were already in the
original proof_deps. The H9 advisory about the proof-plan imports is recorded:
they remain ordinary imports, as required by stages/2-statements.md §3.7 for the
stated proof dependencies; they do not supply extra hypotheses or public notions.

The repaired five records were checked against the complete source definitions,
not only the declaration names. Their typed ring and scheme universes remain
unchanged. In particular the quotient mate still uses the inverse comparison;
the closed transported counit still uses the actual comparison counit; direct
reduction still transposes the reduction unit and the normalized restriction
comparison. No invertibility assertion is added to a definition.

## New nodes

`def-sf-closed-finite-counit-transport` records the identity-compactification
comparison, exact termwise comparisons, and transported closed counit already
constructed in `Sheaf.Paper.ClosedFiniteAdjointCounitTransport`. It owns
`compactSupportIso`, `termwiseIso`, `proTermwise`, `closedComparison`, and
`transportedCounit` in namespace `AlgebraicGeometry.ProEtale.ClosedFiniteTransport`.
Its source is localization (2)--(3), identifying the finite exceptional adjoint and
its counit. The nonempty complement is never assumed; finite coefficient rings and
a quasi-compact open complement match the source signatures. It asserts no ambient
pro-etale exceptional adjunction. The full DAG Lean-record scan found only the
old theorem owner, so this is existing-definition ownership, with no new Lean code.

`def-sf-etale-exceptional-quotient-mate` records
`AlgebraicGeometry.Etale.etaleCoefficientQuotientMate` in
`Sheaf.Paper.EtaleSystemQuotientNormalization`: for specified compact-support
adjunctions and scalar comparison q, it is the right-adjoint mate of q inverse.
Its source is the finite coefficient counit normalization in localization
(2)--(3), with the existing implementation citing Zheng Construction 2.26.
The input comparison and adjunctions remain explicit data; no invertibility of
the mate, flatness or finite-Tor assumption is built into this definition.
No definition node previously owned this declaration.

`def-sf-finite-coefficient-direct-image-map` records
`AlgebraicGeometry.ProEtale.finiteCoefficientChangeDirectImageMap` in
`Sheaf.Paper.FiniteCoefficientDirectImage`. Its source is the closed direct-image
coefficient comparison needed in localization (2)--(3). It defines the map by the
B-geometric adjunction transpose of the scalar extension of the A-counit. The
existing existsUnique theorem determines that map uniquely; the definition is
not a choice from uncharacterized existence. The definition is valid for arbitrary
rings and complexes; the finite/constructible isomorphism theorem is separate.
The source file and DAG scan found the map recorded only in a theorem node.

`def-sf-integral-direct-reduction-map` records
`WeilConjectures.SfExceptionalReduction.directReduction` in
`Sheaf.Paper.SfExceptionalReductionTransitions`. Its source is the integral
coefficient comparison paragraph of localization (2)--(3). The map transposes the
source reduction unit followed by the canonical completed/finite restriction
comparison. It does not assume the map invertible, or restrict f to closed
immersions. The ring, extension, positive exponent n+1, actual completed sheaves,
scalar adjunctions and ordinary derived images are all introduced in its statement.
The DAG scan found no definition node carrying this canonical map.

`def-sf-etale-compact-scalar-map` records
`AlgebraicGeometry.Etale.compactScalarMap` in
`Sheaf.Paper.EtaleCompactScalarCoherence`. Its source is the finite coefficient
compact-support comparison in localization (2)--(3). This packages the existing
components `ExceptionalCoefficients.compactSupportMap` as a natural transformation;
that component construction remains owned by the cited
`def-per-exceptional-coefficient-maps`. No duplicate component map or invertibility
hypothesis is introduced. This packaging had no definition-node owner.

All five reuse the same actually run repair searches, retained verbatim in each
node's mathlib_searches and in searches.jsonl. LeanSearch for canonical closed
exceptional counit / pro-etale scalar maps returned eight generic Mathlib
adjunction/closed-immersion declarations; LeanFinder for scalar direct-image
projection and exceptional quotient returned eight unrelated adjunction/condensed
maps; Mathlib grep of the five actual names returned zero. Exact rg over
WeilConjectures returned no match, while Sheaf located the five implementations
and their source docstrings. The full DAG Lean-record scan showed no definition
ownership of these interfaces. Blueprint_refs ancestor gives
`prop-sf-localization-all-stages`; its searches for quotient (154 results), counit
(195 results), and compact support scalar (zero) contain no blueprint definition
of these canonical maps. Each new node cites its actual underlying notions and
records the same ancestor with this item's id prepended to via.


## H7 repair of returned head 56ed53425251

The return accepts the mathematical statement and all five new existing:true
ownership records. Its sole refusal is that proof_deps gained three entries
without a statement correction. Restored proof_deps exactly, in order, to the
current base's 32 entries, removing `def-sf-integral-strict-reduction-model`,
`lem-coef-finite-direct-image`, and
`lem-sf-exceptional-reduction-transition-comparison`. Removed the unused ordinary
import `Sheaf.Paper.IntegralStrictReductionModel`. All other imports, all five
new nodes, statement dependencies, the mathematical statement, all declaration
signatures and bodies, and the proof docstrings are retained.

Repair second reading by Q76: compared the retained sandbox against the current
shared node before editing; its only non-Lean metadata differences were stmt_deps
and the three added proof dependencies. Checked the restored list equals the base
list byte for byte after JSON serialization and has 32 entries. The removed import
was the only occurrence of IntegralStrictReductionModel in the Lean file. The
accepted clause-by-clause reading of the unchanged theorem statements and the
five ownership records therefore carries over; the existing edge-case audit also
continues to apply. No statement correction is made or claimed.

The exact merge validator `node_fields.check_statement_change(base, sandbox)`
returns `[]` after this repair; the reported H7 refusal is eliminated.
