## Worker report

Item: lem-pur-isomorphism-strict-integral-exchange-normalization. Module:
`Sheaf.Paper.PurStrictIntegralExchangeNormalization`. Its only postponed theorem is
`AlgebraicGeometry.Scheme.purStrictIntegralExchangeNormalization`; the other
twenty-five declarations are explicit constructions or propositional expansions of
this node. No theorem is proved and no definition has sorry data. No source
statement was changed, no dependency was rebound, and four definition-owner DAG nodes were added. They record existing declarations;
no Lean implementation of an existing notion is copied. Additional statement
dependencies identify the landed owners for the remaining canonical helpers.

The latest blueprint source read is
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/prop-pur-weil-equivariance-compatibilities.proof.md`,
together with the extracted argument in this DAG node (fifteen proof steps).
The module docstrings identify this constituent compatibility and its step ranges.

Hypothesis and clause correspondence:

- Finite field, its algebraic closure k, ell different from its characteristic,
  and finite E/Q_ell are exactly `P : WeilConjectures.PurityFiniteSetting.{t}`.
  `PbcIntegralRing P.coefficients.l P.extension` and `pbcIntegralDatum` are the
  published canonical ULift presentation of O_E, its principal uniformizer
  ideal, and its quotient tower. This raises only coefficient size, preserving
  the small pro-etale site's object universe t+1 and morphism universe t.
  The tower's Lean index n denotes the paper's n+1, so no quotient at exponent
  zero replaces the stated positive-exponent quotients.
- The main geometric clause is `PurStrictIntegralGeometricNormalization P`.
  X and Y have `Over (Spec (.of P.field.k))`, separatedness, local finite type
  and quasi-compactness of their structural maps. `f.IsOver` supplies k-linearity;
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` render separated
  finite type. All coherence clauses have the same source geometry with base
  `Spec (.of P.field.k)`.
- Underlying-scheme isomorphisms g, g prime and g bar have `IsIso` binders.
  No `IsOver` is imposed on them or on their target schemes. The two supplied
  chosen squares `sp` and `sj` express exactly the proper and open Cartesian
  squares of the chosen base-changed compactification. A compactification
  includes its proper/open structures and factorization. In a tower, the
  existing `CompositionBaseChange` records every required Cartesian face.
- `r`, `a`, `ha` present a finite generating tuple of the actual ideal; they
  are the published completion interface, not a new ideal. `K` belongs to
  `(cbcCompleteProperty d X r a ha).FullSubcategory`, exactly the domain of
  `completedCompactSupportExchange`. The proper input is literally
  `((cbcJ d c.i).obj K.obj)`; M is not independently chosen.
- G is the canonical ordinary completed-ring pullback `d.pull`. Its exact
  strict counterpart is `d.towerPull`. The predecessor node identifies these
  with inverse image under scheme isomorphisms and its coefficient action.
  All reductions are the actual `completedReductionTower`, not arbitrary towers
  with selected isomorphic evaluations.
- In `PurIntegralProperNormalization`, the first equation is
  `exchangeRealizationH.hom >> r = R.map e >> exchangeRealizationHPrime.hom`.
  Here e is literally `purReindexingDerivedMate`, whose body is the canonical
  `proEtaleAmbientRingedExchange` with d's four coefficient identifications.
  The r component is `(purReindexingRingedSquare d sq).exchangeTowerMate.app
  ((completedReductionTower X d).obj M)`. The second equation is
  `d.towerV' sq M = r`. These are morphisms in the derived category of actual
  completed-ring strict diagrams, retaining every transition before Rlim.
- The remaining proper conjuncts say the two `ordinaryToCompleted` quotient
  units are invertible and give the commuting proper rectangle
  `unit_g >> d.completedExchange sq M = e_M >> push_p'.map unit_gbar`.
  `d.completedExchange` is the recorded proper reconstruction, including
  precisely its `directImageRlimIso` inverse. Thus no unspecified replacement
  of that comparison, or choice of reconstruction isomorphism, occurs.
- `PurIntegralSupportNormalization` includes that proper statement and the
  invertible quotient unit for g prime. It equates `cbcDatumOrdinaryExchange`
  with the published `cbcBeta`, whose inverse is the transpose `cbcBetaInv`
  of the pulled-back open unit. Its next equation identifies the actual
  `cbcRealizationOpenFactor` after the quotient units with this same beta.
- Its last equation identifies `completedCompactSupportExchange` with
  `purIntegralReindexingExchange`, with the two canonical quotient units at
  the endpoints. The latter is literally whiskering of the proper mate by
  j_!, followed by whiskering beta by Rp'_*. Universal quantification over
  K states the equality componentwise on the full complete domain; both sides
  are built from the published natural maps, so this is equality of their
  natural transformations on that domain.
- `PurIntegralStrictMapNormalization` identifies the strict proper mate formed
  from the explicit pullback square with the predecessor's same reindexing
  mate, and writes the inverse open exchange as the actual adjunction
  transpose of the pulled-back open unit. These equations ensure the strict
  maps used below have the specified normalization, rather than arbitrary
  comparisons with the correct endpoints.
- `PurIntegralStrictHorizontal` writes the identity and successive-isomorphism
  equations in the derived categories of completed-ring strict towers.
  `PurIntegralTower.pullId` and `pullComp` are built from the recorded ordinary
  coefficient identity/composition maps and derived localization. The
  successive equation compares exchange along y' y with the two exchanges,
  including the canonical pullback compositor at both ends. It is universally
  quantified on entire strict towers; no evaluation-faithfulness premise occurs.
- `PurIntegralStrictVertical` writes the natural-transformation interchange
  for compatible triangles T,T prime and `CompositionBaseChange`. The explicit
  `PurIntegralTower.composition` is the proper mate of the strict open beta,
  followed by open and proper compositors, as required for the compatible
  proper/open tower. The first conjunct asserts its invertibility only when
  the specified scalar restrictions of every level have `ScalarEtaleOrigin`.
  These witnesses contain bounded-below etale models, retaining that domain.
  The second conjunct is the interchange equation itself, before Rlim.
- `PurIntegralStrictReduction` now states the actual compact-support exchange
  square: `exchange(R K) >> exchangeReductionTarget.hom =
  exchangeReductionSource.hom >> R.map(purIntegralReindexingExchange K)`.
  It also states the compatible-tower composition square:
  `composition(R K) >> supportReduction.hom =
  compositionReductionSource.hom >> R.map(cbcTowerCompositionMap K)`.
  Both are equalities before finite evaluation. Each has the explicit finite
  reduction square at every n, using `finiteCorner` and the actual projection
  `d.projection T n`; this is scalar extension along O_E to A_(n+1), followed
  by restriction of its scalar action, not a comparison with an arbitrary tower.
  `supportReduction` is `towerPush.mapIso(cbcRealizationReduction.symm)`
  followed by the inverse proper projection. The source and target comparisons
  additionally use exactly `d.reductionTowerPullbackIso`. Hence all corners are
  the fixed open-tensor, proper projection and pullback/tensor comparisons of
  coefficient reduction. The compatible etale-origin domain remains on the
  composition square.
- The same predicate includes the canonical `pullId` and `pullComp` reduction
  equations. Together with the natural exchange and composition squares they
  transport the strict identity, horizontal-pasting and vertical-interchange
  equations, with their specified unitors and compositors, under reduction.
  It also states all four finite proper-arrow equations with
  `d.fourArrows sq M hM W n`. Their corners are the explicit
  `properFiniteCorner d sq M hM W n i`, composed from the named projection,
  pullback/reduction, finite evaluation and `chi` comparisons; there is no
  existential corner isomorphism. The complete hM and finite etale-origin W
  retain precisely the bounded domain of those arrows.
- The open reduction clauses retain `res(Omega) >> b = a >> beta` on strict
  towers and add the actual finite open square with
  `cbcReductionStrictExchange`, `cbcSourceFiniteComparison`,
  `cbcTargetFiniteComparison`, and `cbcFiniteExchange`. The latter is the
  fixed open-unit mate at the quotient. The canonical finite source/target
  identifications are uniquely characterized by their K-flat counit equations.
  The proper four-arrow and finite-open equations identify the exchange square
  above with the proper/open exchange at the finite coefficient. Identities
  and pasting are preserved by these natural comparisons and functoriality.
- `PurIntegralCompletedCoherence` writes the identity, successive-base-change
  and vertical completed equations with exactly `completedPullId`,
  `completedPullComp`, `cbcExchange`, and `cbcTowerCompositionMap`. The
  completion witnesses in the conclusions express preservation needed to
  type these comparisons, rather than additional hypotheses on K. The vertical
  clause retains `PbcHasCompatibleEtaleOrigins` and asserts invertibility of
  both composition comparisons, including on the pulled-back object. It
  retains precisely the bounded compatible origin models of the published
  composition-pasting interface. No assertion is made that evaluation is
  faithful on arbitrary derived morphisms.

Dependency declarations read and reused (the additional owning nodes are explicit
statement dependencies because their helpers occur in the expansions):

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting` (and its recorded canonical helper declarations where used).
- `def-weil-pbc-cartesian-square`: `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `AlgebraicGeometry.ChosenCartesianSquare` (and its recorded canonical helper declarations where used).
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement` (and its recorded canonical helper declarations where used).
- `def-cbc-completed-exchange-map`: `Sheaf.Paper.CompletedCompactSupportExchange`, `AlgebraicGeometry.Scheme.completedCompactSupportExchange` (and its recorded canonical helper declarations where used).
- `lem-weil-pbc-profinite-coefficient-inverse-image`: `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`, `AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image` (and its recorded canonical helper declarations where used).
- `prop-weil-pbc-direct-image-limits`: `Sheaf.Paper.CompletedDirectImageLimits`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso` (and its recorded canonical helper declarations where used).
- `lem-cbc-completed-extension-zero-comparison`: `Sheaf.Paper.CompletedOpenExchangeTransport`, `AlgebraicGeometry.Scheme.completedOpenExchangeComparison` (and its recorded canonical helper declarations where used).
- `lem-cbc-strict-tower-proper-open-calculus`: `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`, `AlgebraicGeometry.ProEtale.StrictTower.normalizedProperOpenCalculus` (and its recorded canonical helper declarations where used).
- `lem-fix-operation-reduction`: `Sheaf.Paper.BasicOperationsCoefficientReduction`, `WeilConjectures.basicOperationsCoefficientReduction` (and its recorded canonical helper declarations where used).
- `lem-cbc-complete-proetale-composition-pasting-coherence`: `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting`, `AlgebraicGeometry.ProEtale.StrictTower.compositionPastingCoherence` (and its recorded canonical helper declarations where used).
- `lem-pur-isomorphism-completed-reduction-reindexing`: `Sheaf.Paper.PurCompletedReductionReindexing`, `AlgebraicGeometry.Scheme.purCompletedReductionReindexing` (and its recorded canonical helper declarations where used).
- `lem-cbc-compactifiable-compatible-tower`: `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`, `AlgebraicGeometry.exists_compactifiable_compatible_tower` (and its recorded canonical helper declarations where used).
- `def-cbc-completed-strict-open-exchange`: `Sheaf.Paper.CompletedStrictOpenExchange`, `AlgebraicGeometry.Scheme.cbcStrictExchange` (and its recorded canonical helper declarations where used).
- `lem-weil-pbc-completed-ordinary-comparisons`: `Sheaf.Paper.CompletedOrdinaryComparisons`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.integralRingIso_comp` (and its recorded canonical helper declarations where used).
- `def-cbc-strict-tower-composition-maps`: `Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps`, `AlgebraicGeometry.ProEtale.StrictTower.compositionF` (and its recorded canonical helper declarations where used).

- `def-sf-completed-compact-support-calculus-data`: `Sheaf.Paper.CompleteCompactSupportProetale`, `cbcSupport`, `cbcJ`, `cbcBetaInv`, `cbcBeta`, `cbcExchange`, `cbcBaseChangeQuasiCompact`, `cbcTowerCompositionMap` in `AlgebraicGeometry.Scheme`.
- `def-sf-completed-open-factor-presentation`: `Sheaf.Paper.CompleteProetaleStrictTowerRealization`, `AlgebraicGeometry.Scheme.cbcRealizationOpenFactor`.
- `def-sf-strict-exchange-realization-corners`: `Sheaf.Paper.StrictTowerExchangeMateNormalization`, `AlgebraicGeometry.Scheme.exchangeRealizationH` and `exchangeRealizationHPrime`.
- `def-sf-finite-open-exchange-mate`: `Sheaf.Paper.CompletedRingStrictFiniteExchange`, `AlgebraicGeometry.Scheme.cbcFiniteExchange` and `cbcFiniteInverse`.
- `def-cbc-completed-open-scalar-quotient-interface`: `Sheaf.Paper.CompleteProetaleStrictTowerRealization`, `AlgebraicGeometry.Scheme.cbcRealizationJ`, `cbcRealizationTowerAdj` and `cbcRealizationReduction`.
- `def-cbc-completed-scalar-pullback-interface`: `Sheaf.Paper.StrictTowerExchangeMateNormalization`, `AlgebraicGeometry.Scheme.exchangeTowerRes`.
- `def-sf-completed-open-strict-mate-data`: `Sheaf.Paper.CompletedOpenStrictMateIdentification`, `AlgebraicGeometry.Scheme.cbcOpenMateOmega/A/B/Beta`.
- `def-weil-pbc-completed-four-towers`: `Sheaf.Paper.CompletedTowerCorners`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.towerH`, `towerH'`, `towerV`, `towerV'`.
- `def-weil-pbc-four-arrows`: `Sheaf.Paper.FourArrows`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourArrows` and its canonical `chi`/projection interfaces.
- `lemma-weil-pbc-completed-exchange-coherence`: `Sheaf.Paper.CompletedExchangeCoherence`, `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedPullId/Comp`; the corresponding uniqueness statements pin their data.
- `def-weil-pbc-adic-coefficient-datum`: `Sheaf.Paper.AdicCoefficientDatum`, `completedReductionTower`, `completedReductionEvaluation`, `reductionDerivedRestrict` and `AdicCoefficientDatum.reduction` in `AlgebraicGeometry.Scheme`.
- `def-cbc-completed-finite-exchange-coordinates`: `Sheaf.Paper.CompletedFiniteExchangeCoordinates`, `AlgebraicGeometry.Scheme.cbcFiniteReduction` and the normalized finite coordinate model maps.
- `lem-cbc-completed-ring-strict-finite-exchange`: `Sheaf.Paper.CompletedRingStrictFiniteExchange`, `AlgebraicGeometry.Scheme.cbcFiniteComparisons_existsUnique` and its uniquely pinned `cbcSourceFiniteComparison`/`cbcTargetFiniteComparison`. It is cited for these fixed comparisons, not substituted for the item's compact-support exchange/composition statement.

Proof imports retain the tensor pullback, projection mate, ambient exchange,
ringed tensor coherence, open tensor and strict reduction, scalar/limit,
constant-completion and flat scalar restriction interfaces named by the node's
proof dependencies. Mathlib `CategoryTheory.mateEquiv` and its conjugate-isomorphism
API construct the canonical maps; none states this node's complete normalization.

Edge cases checked by reading the actual constructions:

- Identity base changes use the canonical section/tensor unitors, with their
  explicit strict and completed identity equations; identity is not excluded.
- Empty schemes and empty opens satisfy the same geometric binders and use the
  existing exact extension-by-zero; no nonempty-point hypothesis was introduced.
- Zero complexes remain permitted throughout, including vertical origin witnesses.
  There is no nonzero, positive-rank or cohomology nonvanishing assumption.
- Quotients have exponent n+1; the first paper level is retained. All strict
  transitions are part of the diagram objects, including identity transitions.
- The finite ideal presentation allows every finite generating tuple. Its length
  zero is allowed syntactically; for the nonzero uniformizer ideal ha excludes
  precisely the impossible tuple, rather than silently changing the coefficient.
- Semilinear isomorphisms remain allowed: only f and h are over the fixed k.
  No common-coefficient/site-universe equality or extra base-linearity was added.
- Invertibility of vertical comparison maps retains the etale-origin bounds;
  strict equality itself is not inferred from equality of evaluations.

Searches for reuse:

- `msearch.py ... leanfinder "Strict integral compact support exchange for scheme
  isomorphisms equals reindexing in the derived category of strict towers before
  derived limit"`: eight results, unrelated general limit/transition or support
  facts; no complete match.
- `msearch.py ... loogle "CategoryTheory.mateEquiv, Functor.mapIso"`: zero results,
  parser rejected the unqualified second name. Repeated with
  `CategoryTheory.mateEquiv`: twelve results, mates and mate-pasting primitives;
  these supply the construction, not this normalization theorem.
- `msearch.py ... grep "mateEquiv|reindexing" CategoryTheory/Adjunction`: five
  general mate hits, no geometric statement.
- Exact node-id grep in `lean/WeilConjectures` and name searches
  `purStrictIntegralExchangeNormalization|PurIntegralProperNormalization|purIntegralReindexingExchange`
  in both `lean/WeilConjectures` and `lean/Sheaf`: no existing statement.
  Broader strict-tower and reindexing searches located the recorded predecessor,
  strict normalization, open exchange and composition interfaces reused here.

No STATEMENT-DISPUTED issue or correction is claimed.

## Second reading by Q10

The dispatcher explicitly prohibited starting other agents, so this is a second
self-reading with the node and expanded declarations open, not an independent
worker review. The maintainer's independent review remains required.

This pass found and repaired three draft mismatches before delivery: pasting must
use actual completed-ring towers, not just constant-coefficient towers; the finite
reduction comparison must explicitly use the fixed canonical corners and the
actual strict exchange/composition maps; and the coherence predicates must retain the stated finite
field geometric domain. The final predicates use completed-ring strict maps,
the full four-arrow rectangle, and the fixed source geometry. The coefficient
ULift is the published canonical size presentation, and every universe is explicit.
All twenty-six declarations are listed in lean.declarations. The one sorry is the
named main theorem with its complete fifteen-step proof plan and matching DAG node.

Validation: the complete module passed scompile.py, both sandbox and library
presentations, with no compiler errors or unexpected warnings. The final import
visibility and delivery checks are recorded below after the dry run.

## Returned delivery repair

The returned immutable head is `11178be8cca3`. The saved packet's initial dry run
passed mechanically (`12344ca8528`); its mathematical H3 finding required the
substantive changes above, so the unchanged packet was not pushed.

H3: removed every existential alpha corner from `PurIntegralStrictReduction`.
Six explicit helper definitions now construct the support, source, target,
composition and finite comparison corners. The predicate mentions the actual
`PurIntegralTower.exchange` and `PurIntegralTower.composition`, states their
reduction squares both before evaluation and at each quotient, and includes the
canonical identity/compositor reduction equations. The proper/open finite maps
are pinned separately by the four proper arrows and the finite open-unit mate.
`BasicOperationsCoefficientReduction` remains a proof import: its packaged
basic-operation models are not substituted for these actual completed-ring
maps. The fixed comparisons used here are their concrete tensor/mate
realizations (`reductionTowerPullbackIso`, `towerProjection`,
`cbcRealizationReduction`, `completedReductionEvaluation`, finite `chi`, and
uniquely counit-normalized finite open comparisons).

Mechanical definition ownership: added four existing:true definition nodes
below and cited the three previously landed scalar/open definition owners.
Removed the prior packet's four theorem-only additions whose only purpose was
owning plain definitions. The justified ordinary-comparison dependency stays.
The advisory owners for `completedPullId/Comp`, `towerV'` and `fourArrows` are
now explicit statement dependencies too.

The scheme geometry, allowed non-k-linear isomorphisms, complete domain with
M=j_!K, specified H/H', proper direct-image/limit comparison, beta and Ex formula,
completed-ring strict horizontal/vertical clauses, and site/coefficient universes
are retained. No natural-language node statement or proof was changed.

## New nodes

`def-sf-completed-compact-support-calculus-data` records the exact existing
completed support functor, unit-normalized beta, exchange abbreviation, induced
quasi-compactness and compatible-tower composition map in
`Sheaf.Paper.CompleteCompactSupportProetale`. Source: constituent compatibility,
steps 7--14. It records data only, not that module's theorem conclusions.

`def-sf-completed-open-factor-presentation` records the exact existing
`cbcRealizationOpenFactor` in `Sheaf.Paper.CompleteProetaleStrictTowerRealization`:
the published completed open exchange component with the quasi-compactness
instance induced by the compactification. Source: constituent compatibility,
steps 7--9. No realization equation is assumed.

`def-sf-strict-exchange-realization-corners` records `exchangeRealizationH/HPrime`
in `Sheaf.Paper.StrictTowerExchangeMateNormalization`, with exactly the specified
pullback/reduction and projection composites. Source: constituent compatibility,
steps 2--4. Neither rectangle commutation nor exchange normalization is included.

`def-sf-finite-open-exchange-mate` records `cbcFiniteExchange` and
`cbcFiniteInverse` in `Sheaf.Paper.CompletedRingStrictFiniteExchange`: the actual
finite open-unit mate with restriction of its scalar action. Source: constituent
compatibility, steps 7, 13--14. This prevents a further plain helper from being
mistaken for a theorem dependency while retaining the uniquely characterized
finite endpoint comparisons as a justified statement dependency.

For all four nodes, `msearch.py` LeanSearch/LeanFinder/Mathlib grep were run with
"Canonical proper open compact support functor exchange composition and completed
strict reduction comparison corners" and, for the finite mate, "Canonical finite
coefficient open base change exchange inverse unit adjunction mate". The results
were generic categorical facts or unrelated topology/support facts, with no
matching Mathlib notion. Exact-name Mathlib grep returned zero. Exact-name source
searches returned no WeilConjectures declaration, and found the exact published
Sheaf definitions reused above. DAG grep found theorem records but no definition
owners of these particular helpers. `blueprint_refs.py search` for "completed
compact support", "strict exchange realization", "completed open factor" and
"finite open exchange" returned zero. Each node's `mathlib_searches` retains
the actual search outputs and the local search findings. No duplicate module or
new choice is introduced.

Validation: the repaired 26-declaration module compiled via scompile.py in both
sandbox and library presentations, with no errors or unexpected warnings. The
only sorry remains the named main theorem with its fifteen-step proof docstring.

Dry-run repair: the first repaired-packet preflight required the current DAG
shape field `import_flags` on each new definition record. All four now carry
`import_flags: []`; no mathematical field changed. The three theorem-node
advisories concern justified equation/uniqueness interfaces: ordinary coefficient
composition and modulePushId, completed pullback unit/composition uniquely pinned
by their normalization, and finite endpoint comparisons uniquely pinned by
K-flat counit equations. Plain helper maps have separate definition owners.
