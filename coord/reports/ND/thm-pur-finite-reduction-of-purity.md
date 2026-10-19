## Worker report

The item is stated in `Sheaf.Paper.FiniteReductionOfPurity`. The packet retains the earlier worker's quotient, root-chart and canonical-adjunction constructions, repairs the root-chart assembly, adds the omitted affine-orientation clause, and supplies the missing smooth-exchange prerequisite. Every theorem is stated with `by sorry`; definitions have actual composites, recursion, or a choice from a theorem that uniquely determines the chosen map. There is no statement correction or disputed statement.

Hypotheses and clauses, checked against the node:

- The fixed field, characteristic, coefficient extension and positive larger level are exactly `P : PurityFiniteSetting.{u}`. `finiteReductionSetting` retains that datum and changes only its level. `m : ℕ`, `hm : 1 ≤ m`, and `hmn : m ≤ P.level` express exactly the two positive finite indices and their order. `finiteReductionRingHom` is `Ideal.Quotient.factor` on the actual coefficient-extension ideals, using `Ideal.pow_le_pow_right`; it is not a field-extension map.
- The finite reduction is `finiteReduction`, the existing derived extension functor along the induced constant-ring sheaf map, with its smaller scalar action retained. `finiteReduction_preserves_ctf` states its codomain on every finite-Tor constructible input. The ambient intrinsic small pro-etale category is `Scheme.proEtaleDerivedCategory`; no replacement site or equality of site object and morphism universes is imposed.
- Separated finite-type k-schemes are rendered by the `Over (Spec (.of P.field.k))`, `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` instances on their structure morphisms. Morphisms are k-morphisms through `IsOver`. `SmoothOfRelativeDimension d f`, with `d : ℕ`, renders smoothness of pure relative dimension d. The displayed finite-type properties of f follow from this finite-type separated setting and do not exclude a source case.
- `K` lies in the original intrinsic ambient category, and `hK : finiteTorConstructible ... Y K` is exactly membership in D^b_ctf. The source of gamma is the dependency's `compositionShiftedPullback f d`; gamma itself is the dependency's `smoothPurityMap f d K hK`. Its tensor, twist, shift, exceptional and realization coordinates are retained.
- `finiteReductionOfPurity` is precisely the displayed square: reduced gamma followed by `finiteReductionExceptionalComparison` equals `finiteReductionSourceComparison.hom` followed by gamma at the reduced input. The source comparison is an actual isomorphism. The exceptional comparison is fixed by its compact-support/counit transpose, and its separate `..._isIso` statement gives the right vertical isomorphism. Neither comparison is defined from gamma, so the square is substantive.
- `finiteReductionOfAffineOrientation` states reduction of the actual orientation morphism. `finiteReductionEtaleOrientation` is the exceptional adjunct of the uniquely supported-Kummer-normalized Ext class of the zero Cartier divisor. `finiteReductionOrientation` transports that map through the existing comparison adjunction and intrinsic realization. Its source, target and exceptional coefficient maps are independently fixed by root-section and counit equations. The supported-Kummer construction works at exponent ell^n for every positive level; no ramification-index divisibility or flat quotient assumption is introduced.
- `finiteReductionOfSmoothTrace` compares the coefficient-valued `coefficientValuedSmoothTrace` with the smaller trace after the actual compact-support and source comparisons. `finiteReductionOfUnitSmoothTrace` gives the coefficient-unit trace `smoothTrace`, including its scalar-unit comparison. Thus both the arbitrary K and coefficient-unit trace clauses are present.
- `finiteReductionOfCompositionSource` identifies the specified source compositor at both levels. `finiteReductionOfCompositionExceptional` identifies the standing exceptional compositor itself. `finiteReductionOfCompositionCoherence` explicitly reduces the entire three-arrow purity composite, including its inverse exceptional compositor; it does not merely assert that each level separately has a commuting diagram.
- `finiteReductionOfBaseChange` has two equations: one identifies the actual source pullback/tensor/twist map, the other identifies the actual smooth exchange. `finiteReductionSmoothExchange` is literally inverse pulled-back gamma, the independent canonical middle identification, then gamma for f'. The square is `sq : IsPullback u f' f v`. There is no smoothness, flatness or properness hypothesis on v. The properties of f' are the usual Cartesian-pullback properties of f. Both base-change horizontal gamma arrows are the maps already covered by the main purity square, so these two equations cover all four specified edges.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `Ring`, `Coefficient` and the fixed datum.
- `Sheaf.Paper.SmoothPurityMap`: `smoothPurityMap`, `smoothPurityPullback`, `smoothPurityTensor`, `smoothPurityReassociation`, `smoothPurityExceptionalComparison` and the published realization coordinates.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`: `AlgebraicGeometry.ProEtale.derivedTensor`, the existing K-flat total tensor, also used by the source reassociation.
- `Sheaf.Paper.DerivedPullbackTensorHom` and its imported constant-ring operation interfaces: the existing `Scheme.proEtaleRingDerivedExtension`, `Scheme.proEtaleRingDerivedExtensionAdjunction` and constant-coefficient pullback comparisons. Scalar restriction is `Scheme.proEtaleCoefficientRestrictScalars`, with its ordinary derived shift and single-object maps.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` / `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: the standing finite exceptional inverse image. `compositionExceptional` and `smoothExceptionalCounit` use that same object and its standing relative adjunction, rather than a new right adjoint.
- `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`: `diagonalExponent`, its annihilation and invertibility facts, `diagonalTwistEtale`, `diagonalTwist`. The current recorded unrestricted twist module publicly imports the positive finite presentation through PbcCoefficientTwists, and is now imported directly by the root-chart module.
- `Sheaf.Paper.PurityAffineLineOrientation`: `affineLine_orientation` and its supported coordinate-boundary normalization were read. The named canonical orientation here uses the equivalent independent supported Ext-class normalization, including levels not handled by that existential interface. `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer.ordinary_supported_kummer` and `OrdinarySupportedKummerBoundary.SupportedKummerBoundary` fix the supported class uniquely. `OrdinarySupportedKummerSystem.supportedExactDerivedMap` realizes it before exceptional transposition.
- `Sheaf.Paper.SmoothTrace`: `smoothCompactSupport`, `coefficientUnit`, `smoothExceptionalCounit`, `coefficientValuedSmoothTrace`, `smoothTrace`.
- `Sheaf.Paper.PurityCompositionCoherence`: `compositionShiftedPullback`, `compositionSourceIdentification`, `compositionExceptional`, `compositionExceptional_ctf`, `compositionExceptionalIso`; these are the exact three-arrow composition coordinates, including the standing counit-normalized exceptional composition.
- The Mathlib match of `thm-pur-smooth-base-change-coherence` is `CategoryTheory.Iso.hom_inv_id_assoc` from `Mathlib.CategoryTheory.Iso`: the single-level commuting square follows by cancelling the pulled-back gamma inverse in the definition of smooth exchange. It is not itself a cross-coefficient comparison, which is what this item adds.
- `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`, with `IntrinsicFiniteTorsionConstructibility.intrinsicFiniteTorsionConstructible` for bounded constructibility. The scheme-property convention node merely collects the Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` and smoothness properties, with no additional structure to define.

Edge cases checked: m=n uses the actual identity quotient and all identity maps remain in the statements. Level one and arbitrary ramified levels are allowed; no e-divisibility is assumed. The zero relative dimension gives the actual zero tensor power and zero shift. Empty schemes and zero complexes are retained; no geometric point, root chart or nonzero scalar is selected as additional input. Primitive-root tests are nonvacuous because the fixed base is algebraically closed and ell differs from its characteristic; for every primitive ell^n root its ell^(n-m)-power is primitive at level m. Quotient maps may be nonflat; the finite-Tor condition is retained. The base morphism in a square is arbitrary, including identity and nonflat maps. All universes are explicitly declared and `autoImplicit` is false.

Searches retained from the saved packet and repeated during recovery:

- LeanFinder, `smooth purity map commutes with derived reduction of finite coefficient rings`: eight smooth-ring facts, no purity/coefficient-reduction theorem.
- LeanSearch, `smooth purity commutes with derived coefficient reduction`: eight algebraic smoothness/base-change facts, no derived purity result.
- Loogle, `"purity"`: twelve compiler-purity declarations, no cohomological purity.
- LeanSearch, `Primitive root trivializations uniquely characterize canonical derived finite coefficient reduction comparisons of Tate twisted pullbacks`: primitive-root facts only. Loogle, `IsPrimitiveRoot, Functor.mapIso`: no hit (second identifier unrecognized).
- LeanSearch, `canonical finite coefficient reduction of the supported Kummer affine line orientation via the exceptional adjunction`: Kummer field extensions, finite morphisms and affine-coordinate facts only.
- LeanFinder, `primitive root normalized coefficient reduction comparisons for smooth purity and affine orientations`: Fermat/Pythagorean, Weierstrass and polynomial-normalization facts only.
- msearch grep, `finiteReductionOrientation|finiteReductionSourceComparison|finiteReductionRootTrivialization`: zero Mathlib matches. Earlier grep `finite.*reduction|reduction.*purity|smoothPurity` also had zero matches.
- `rg` of the named declarations and the item id in upstream `WeilConjectures` and shared `lean/Sheaf`: no preexisting finite-reduction purity or comparison declaration. Searches for supported Kummer did find the existing ordinary supported boundary/system/theorem, which are reused. DAG searches and `tools/blueprint_refs.py search 'root trivialization'` found no existing root-chart comparison definition. The ancestor query returns this item itself.

The node's proof is followed through bounded flat reduction, independent operation comparisons, supported Kummer boundaries, the diagonal/DNC/vector-bundle chain, the three constituents of gamma, and the explicit trace/composition/exchange composites. In particular the invalid inference that equality of arbitrary derived morphisms can be checked on geometric fibres is not used.

Validation: the required dry run first reported a missing report, then unowned scratch modules. The scratch modules were retained as `.lean.txt` under scratchpad and excluded from the packet. Subsequent single-file compilation diagnosed expensive root-chart elaboration. The canonical chart uses typed intermediate factors, as the published composition interface does. A proof-term diagnostic identified expensive specialization of `compositionEtalePowerSuccessor` and `existsUnique_finiteReductionTensorUnit` at the actual quotient. `finiteReductionEtaleRootPowerChart` and `finiteReductionTensorUnit` perform these operations generically in the chart-calculus module before the finite quotient is substituted. The power chart is the actual ordered zero/successor recursion. The chart-calculus and root-chart modules passed the private-overlay compile with this repair; the remaining final compilation and dry-run results are recorded below after completion.

## Second reading by ND

Author self-check under the dispatcher brief; no independent agent was started. I compared the node and the source files again, clause by clause. The saved packet omitted affine orientations, had no report, included unowned experimental modules, and expanded the large root chart directly. I added the full positive-level supported-Kummer orientation equation, archived the experiments, supplied this report and factored the chart with a unique normalization. I also checked the canonical smooth-exchange specialization and the finite-twist interface; their current-source disposition is described below. The main node's statement, proof and proof dependencies remain unchanged. Every reduction comparison is fixed independently of the purity equation it is used to state. The actual arbitrary-base-morphism smooth exchange is the purity composite, and both the source and exceptional composition comparisons appear explicitly. The maintainer provides the independent mathematical review.

## New nodes

`def-pur-finite-reduction-chart-calculus` defines ordered tensor-power chart assembly, native tensor-unit/shift maps and exact-derived comparison-unit maps. Its source is reduction proof Step 1. Generic categorical operations exist, but this ordered assembly and its published/native presentation bridge were not named notions in the DAG or library. The searches listed above found no matching finite-reduction chart construction; the existing tensor, unitor and shift APIs are reused.

`def-pur-finite-reduction-root-charts` defines the actual quotient functor and independent primitive-root trivializations of its shifted pullback source. Constant scalar sections fix the rank-one chart uniquely, ordered tensor recursion fixes its powers, and the four canonical factors fix the source chart. Its source is reduction proof Step 1. These are coordinate comparisons absent from the existing smooth-purity interface, which already defines the tensor source itself and is reused. No second twist or inverse-image functor with different data is introduced.

`def-pur-finite-reduction-comparisons` defines the pullback, shifted-source, coefficient-unit, compact-support and exceptional coefficient maps. Their normalizations are the ring-section quotient, the derived pullback mate, the primitive-root source equation and the compact-support counit transpose. Its source is reduction proof Steps 1 and 2. The ordinary scalar restriction and proper/open comparison APIs exist and are used, but they did not give named finite-level comparisons in the exact intrinsic coordinates of gamma. The node records the same searches and the precise normalized constructions.

`def-pur-finite-affine-orientation-comparison` defines the independently fixed input and zero-section exceptional comparisons for the supported-Kummer orientation. Its source is reduction proof Step 3. `ordinary_supported_kummer` supplies the unique supported class and is reused; the existential affine orientation theorem does not name the reduction comparisons. This node adds those actual maps and their full-positive-level orientation coordinates, rather than choosing a generator arbitrarily.

## Dependency modules

`def-coefficient-twists-detailed` needs no delivered repair against the current base. Its recorded `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` now publicly imports `PbcCoefficientTwists`, which imports `FixedFinitePositiveCoefficientTwist`. Thus it already supplies the full signed/integral/rational/common-stage interface and the exact positive finite presentation used here. The root-chart module directly imports that current recorded module. The saved lean-only rebind was removed after the preflight identified its primary-declaration/module mismatch; every previously published twist interface is retained.

`def-pur-smooth-pullback-exchange` now records upstream `AlgebraicGeometry.Etale.smoothPullbackExchange`, which accepts supplied dualizing orientations and tensor isomorphisms in the ordinary etale category. That interface does not specialize those inputs to the canonical diagonal and tensor maps on the intrinsic pro-etale finite-Tor category. `Sheaf.Paper.FiniteSmoothPullbackExchange` supplies its literal canonical composite and the required input-preservation and invertibility interfaces. The middle source identification is fixed independently by the same pullback compositors, tensor root charts and shifts as the node specifies. This is an existing prerequisite node, not a new substitute notion. Only its `lean` field is added, and the item explicitly cites it.

The chart-calculus module registers the existing Mathlib `Sheaf.monoidalCategory` instance globally, so its native derived-unit expressions remain readable in importing modules. It introduces no second monoidal structure or file-local instance.

The exact-derived pullback compositor is named `finiteReductionPullbackPresentationNative`. Its body supplies the published realization additive instances before composing the existing exact-derived comparison maps; this avoids a failed instance lookup in the statement without adding an additive hypothesis or a file-local instance.

Recovery self-check (2026-10-18): I read the newly attached upstream
`WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction` through the prescribed
source wrapper. Its theorem takes arbitrary coefficient functors, orientations,
tensor formulas and the constituent reduction equations as hypotheses; it does
not state this node's canonical quotient comparison or all its coherence clauses.
The explicit packet is therefore retained. The dependency copy was refreshed so
that only its `lean` record differs from the current base.

I also found and removed an incorrect saved helper asserting that the affine-input
chart was the unique isomorphism satisfying `True`. Rank-one objects generally
have multiple automorphisms. `finiteReductionOrientationInputChart` now is a real
composite: `finiteReductionShiftedLineChart`, comparison inverse image and its
shift map, then intrinsic realization and its shift map. There is no existence
choice in this chart and no new mathematical assumption. I supplied missing
source/proof docstrings for the affine-space property helpers and the exact
pullback shift instance. Explicit return types were added to comparison helpers
to reduce the checking cost of their inferred interfaces.

The explicit comparison signatures passed server confirmation (54.3 seconds for
`FiniteReductionComparisons`, no warnings). The primitive-root and chart-calculus
modules also passed that confirmation. Full-packet validation follows below.

The heartbeat diagnostic isolated kernel checking of `finiteReductionUnitComparison`.
Its degree-zero scalar-adjunction composite has now been factored as
`finiteReductionUnitAdjunct` for abstract finite rings before specializing the
quotient; the specialization uses the same section map and canonical unit models.
The construction and normalization are unchanged, and no linter is disabled.

Full-packet compilation then diagnosed a missing `IsOver` instance for the affine
zero section. Two actual instance definitions now use the existing
`AffineSpace.zeroSection_comp_over` and
`CategoryTheory.homIsOver_of_isOverTower`; no hypothesis is added. The source
search found those exact existing declarations and no registered zero-section
instance in the source or side library.

Further profiling showed expensive kernel checking of the saved unit-model
existence statement as well. `finiteReductionUnitModel` now constructs that
comparison directly for an abstract finite ring from the same three canonical
factors, so the unnecessary existence theorem was removed. The single-object
scalar adjunct is assembled for an abstract exact functor and its supplied
adjunction, and is then specialized to the published coefficient adjunction.
This preserves the original scalar-adjoint normalization by naturality.

The full compiler also reached a duplicate between the legacy and finite-coefficient
pro-etale comparison APIs (`derivedComparisonAdjunctionPlus`). I removed these four
proof-only imports from the main module: `PuritySectionInvariant`,
`PurityDiagonalBaseChange`, `PurityDncInvariance` and
`AlgebraicGeometry.FiniteCompactProjectionFormula`. Their source imports the
retired legacy tensor/exceptional or `ExchangeProjection` interfaces. The finite
canonical declarations required by every statement remain imported; the supplied
exchange/projection interface is retained. These proof-only imports must be
revisited after the legacy duplicate modules are retired. No DAG dependency was
removed or changed.

Recovery self-check (current run, 2026-10-18): retained all six saved modules. The current upstream smooth-exchange signature and docstring were checked; its supplied ordinary-etale orientation inputs do not replace the packet's canonical intrinsic specialization, so the dependency repair is retained with an updated note. The chart-calculus record previously included the recursive body and the next declaration; its `lean.statement` now contains just the verbatim recursive declaration signature. Existing node copies differ from the base only in `lean`, and the item additionally gains the stated prerequisites.

The self-check also removed a hollow `CommShift` instance from the saved exchange module: it now composes the existing termwise exact-derived shift structures of the realization inverse, ordinary pullback and realization functor. Its shift isomorphisms are actual data; no theorem or hypothesis is added.

The required initial dry run reached the main theorem file and failed with the duplicate legacy `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`. Import-closure inspection identified two remaining proof-only legacy paths: `CohomologicalSmoothnessComparison` and `CohomologicalSmoothnessTheorem`, through legacy derived Tor amplitude. Those imports were removed; the canonical tensor/purity declarations remain supplied by `SmoothPurityMap`. The mathematical proof dependencies remain recorded in the DAG and their duplicate-bearing modules await library cleanup.

Validation recovery: all six delivered Lean modules passed the refreshed full server compilation, including the canonical shift-data repair and the main theorem after removal of the conflicting legacy proof imports. Preflight then identified four incorrect blueprint `via` arrays (the item is its own blueprint ancestor, so each must be empty) and a stale twist-record rebind. The arrays are repaired. Current-source inspection showed that the recorded unrestricted twist module already reexports the positive finite interface; the unnecessary dependency copy was removed and that module is imported directly. A fresh dry run follows.

Final validation (2026-10-18): the required `deliver2.py ND thm-pur-finite-reduction-of-purity --no-push` returned `OK (dry run)` at bfe973a335. All six delivered files compiled cleanly, and the complete server preflight passed. The item statement, proof and proof dependencies are unchanged; the only delivered dependency repair is the canonical intrinsic smooth-exchange specialization.
