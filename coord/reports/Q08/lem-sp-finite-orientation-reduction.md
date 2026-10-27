## Worker report

The module `Sheaf.Paper.FiniteOrientationReduction` states the clauses of
`lem-sp-finite-orientation-reduction` using the existing canonical finite coefficient
and strict varying-coefficient tower interfaces. Every theorem has the whole proof
`sorry`, with the source and complete proof plan in its docstring. The helper definitions
contain actual constructions. No node statement, dependency, or proof plan is changed.

The finite map equations are written in the recorded ordinary-etale presentations of the
pro-etale constructible operations. This is the presentation used by
`ReductionCompatibilities.reductionCompatibilities_purity` itself. The module also states
`canonical_purity_at_unit` directly for the recorded pro-etale
`PurityFiniteSetting.smoothPurityTensorMapInPresentation`; the displayed formula includes
the pullback, monoidal site and unit comparisons and ends in the inverse of the actual
`diagonalDualizingObject`. Thus it is not an assertion about arbitrary endpoint isomorphisms.

Hypothesis and clause correspondence:

* The finite field, its algebraic closure, characteristic p, coefficient prime l and l != p
  are `FiniteFieldDatum`, `Fact l.Prime`, and `hl : l ≠ D.p`. The uniformizer comparison
  uses `P.field`, `P.coefficients`, and `P.extension`, from the recorded
  `PurityFiniteSetting`. The extension there is a finite subextension of the fixed
  algebraic closure, as in the project's coefficient convention. The reduction and tower
  statements allow any `E : Type u` with `Field`, `Algebra (Padic l) E` and
  `FiniteDimensional (Padic l) E`.
* The valuation ring and uniformizer are the actual
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`.
  `v : (...)ˣ`, `hv : (l : O_E) = v * uniformizer ^ e`, and `he : 1 ≤ e`
  render the displayed ramification factorization. `setting P e he n` changes only the
  positive level to `e*(n+1)`. `coefficient_ideal` states equality of the two actual ideals;
  `coefficientEquiv` is `Ideal.quotEquivOfEq` of that equality, induced by identity on O_E.
  In particular no arbitrary ring equivalence identifies R_n with A_(E,en).
* `X,Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, and the
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` instances on their structure maps
  are the separated finite-type k-scheme hypotheses. The morphism is `f` with `IsOver`,
  `IsSeparated` and `SmoothOfRelativeDimension d f`; `d : ℕ` means d >= 0.
  The explicitly installed `IsNoetherian`, `HasCompactification`,
  `LocallyOfFiniteType f`, `QuasiCompact f` structures are proof-valued consequences of
  those original hypotheses, required by the dependencies' normalized-map interfaces.
  They do not assert a stronger geometric domain. No smoothness hypothesis is needed
  in the universal unit calculation; its smooth specialization is exactly the clause
  used here.
* All indices `n,m : ℕ` are predecessors of the paper's positive indices: n means n+1.
  `m ≤ n` therefore renders precisely `1 ≤ m_paper ≤ n_paper`. The actual ring is
  `SpTowerShriek.R l E n = O_E / (l)^(n+1)`; the actual quotient map is
  `SpTowerCalculus.quotient l E hmn`. The hN/hM arguments are proofs that the displayed
  powers vanish in these quotients, not new coefficient restrictions. They are the
  quotient equations supplied by `SpTowerClasses.coefficient_annihilates` (also exposed
  as `SpTowerP1.levelAnnihilates`).
* The finite shifted line is the recorded `FiniteSmoothPurity.line`, and at the
  uniformizer level it is `P.diagonalTwistEtale`. These are the ordered tensor product
  of shifted positive Kummer lines, with zero-fold product the coefficient unit.
  `CoefficientLineComparison` fixes the scalar/root-generator map, power map on roots,
  derived single-complex comparison and its tensor-power extension. The latter's
  `tensorPower d` is the canonical Tate reduction, including d=0. There is no new twist.
* The inverse diagonal orientation is `alpha.inv`, where `alpha` is constrained by
  `DiagonalOrientationNormalization` at uniformizer level or `OrientationNormalized`
  for the direct finite-ring construction. These are the exact normalization predicates
  of the recorded diagonal theorem and general-ring theorem, respectively. The first
  fixes each etale coordinate counit, the second fixes diagonal, t=1 Rees specialization
  and inverse integration. These are presentations of canonical orientations, not
  additional assumptions on a freely chosen map. `ordinaryOrientation` changes from the
  degree-zero single coefficient unit to the monoidal unit using `smoothPurityUnitIso`.
* `coefficient_unit_purity` first states theta at the coefficient unit is the identity:
  after pulling back the unit its value is the left unitor. Its second conjunct states
  gamma at the unit is `alpha.inv`, after inverse left unitor and inverse pullback-unit
  constraint. `canonical_purity_at_unit` states this again for the actual recorded
  pro-etale purity map and the actual `diagonalDualizingObject`, including the specified
  comparison maps. `smoothPurityMap` is this tensor form preceded by its recorded tau;
  the node's phrase 'under tensor-unit identifications' is precisely this source change.
* `uniformizer_orientation_agreement` identifies the direct general-ring inverse
  orientation with the one at index e*(n+1), after the identity-induced quotient
  equivalence. `uniformizer_purity_agreement` states equality of the full gamma maps
  on every `boundedConstructibleFiniteTor` input, with precisely the ordinary
  scalar/pullback/twist balancing and the exceptional counit mate. This covers the
  general-ring agreement clause for the purity comparison, including general allowed K.
* `finite_orientation_reduction` is the requested equation
  `(alphaN.inv)_Rm ≫ c = TateReduction ≫ alphaM.inv` in Lean's diagrammatic composition
  order. `dualizingScalarMap` is the actual `mateMap` at the coefficient unit followed
  by the canonical multiplication unit identification, not a supplied comparison.
  Consequently, after identifying the Tate sources it is precisely
  `c_(n,m)(R_(n,Y)) ∘ (a_n)_Rm = a_m`.
* The actual tower category is `SpTowerCalculus.C`, the full subcategory of the
  ordinary derived category of `spCoefficientTowers` with one common cohomological
  and one common Tor interval. `b`, `o`, and `q` are its already supplied operations,
  abelian realization, and section-preserving scalar coordinates. `unit_tower_mem`
  asserts membership for the genuine coefficient tower transported by the specified
  inverse realization. It makes no normalization assumption on arbitrary inputs.
* `G`, `adj`, and `lv : SpTowerGluing.Levels ...` are exactly the tower right adjoint,
  adjunction and finite evaluations supplied by `det-sp-tower-gluing`.
  `unit_tower_reduction` quantifies a whole-tower identification of K with the
  coefficient tower, not separate level isomorphisms. It asserts invertibility of its
  actual input reduction, then identifies the reduction of G K with the exact
  `SpTowerGluing.coefficientMate` after canceling that scalar-unit identification.
  The displayed equation retains `SpTowerCalculus.reduction ... (G.obj K).obj`,
  `lv.comparison`, and `lv.right.map` of the inverse input reduction. This states the
  final clause for actual omega transitions and does not silently replace them by c.

Dependency declarations read and reused (module, names):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, `.CoefficientDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public
  `CoefficientExtension` import): `Padic.finite_coefficientExtensionRing`,
  `coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
  `coefficientExtensionIdeal`, `coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  `SmoothOfRelativeDimension`. The scheme-property dependency is explicitly a convention
  collector; its named Mathlib properties are used directly.
* `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spEllIdeal`, `spCoefficientTowers`;
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`;
  `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spFiniteConstructibleTorCategory`,
  `spConstructibleTorTowers`, `spDerivedCoefficientEvaluation`.
* `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`. Its ordinary-etale analogue underlies
  all the stated ordinary comparison formulas; it is not a separate tensor definition.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` and the diagonal theorem's
  public `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`: the original signed twists
  `sfQbarTwistingFunctor` and the used finite positive presentation
  `PurityFiniteSetting.diagonalTwistEtale`, `.diagonalTwist`.
* `Sheaf.Paper.SmoothPurityTowerGluing`: `SpTowerGluing.Levels`, `.coefficientMate`,
  `.level`, `.support`, `.tower_gluing`; its public interfaces give
  `SpTowerCalculus.C`, `.realization`, `.quotient`, `.reduction`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded finite derived operations and
  higher-stage operation reexports; the recorded primary declaration
  `commonStageDerivedInternalHom_existsUnique` concerns the unused Qbar stage.
  Finite pullback is used through `ordinaryFinitePullback` and `smoothPurityPullback`
  as in the recorded finite purity-map dependency.
* `Sheaf.Paper.PurityDiagonalDualizingObject`:
  `PurityFiniteSetting.DiagonalOrientationNormalization`,
  `.existsUnique_diagonalDualizingObject`, `.diagonalDualizingObject`.
* `Sheaf.Paper.SmoothPurityMap`: `smoothPurityUnitIso`, `smoothPurityTensor`,
  `smoothPurityComparisonTensor`, `smoothPurityPullbackComparison`,
  `smoothPurityTensorMapInPresentation`, `smoothPurityMap`.
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison` and its standard upstream
  `UpperShriekCanonicalMaps`: `finiteComparedTensorClause`,
  `Etale.dualizingComplexTensorMap`; its source-order version is the published
  `Etale.smoothTensorDualityMap` used in the unit calculation.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`,
  `.projection`, and the compactification projection composite.
* `Sheaf.SecSmoothPurity.FiniteGeneralRing`: `finiteGeneralRingSmoothPurity`,
  `finiteGeneralRingPrimeSetting`, `finiteGeneralRingUnit`.
* `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor` and the
  generator-normalized scalar/Tate comparisons; the fixed-ring presentation is the
  published `FiniteSmoothPurity.ordinaryScalar`, `CoefficientLineComparison.tensorPower`.
* `Sheaf.SecSmoothPurity.ReductionCompatibilities`: `reductionCompatibilities_purity`;
  the public coefficient-map owner `Sheaf.Paper.FiniteSmoothCoefficientArrows` gives
  `FiniteSmoothPurity.gamma`, `pullbackTwistComparison`, and its public
  `ExceptionalCoefficientComparison` gives `ExceptionalCoefficients.dualizingScalarMap`.
* Proof-only imports `Sheaf.Paper.ProjectionMateExact`:
  `SheafOfModules.ringedProjectionMateExact`; and
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`:
  `derivedOpenImmersionLowerShriekProjectionIso`.

Edge cases checked before and after drafting: d=0 uses the genuine zero-fold line,
pullback-unit comparison and unitors; equal indices m=n are included and use the scalar
unitor; m=n=0 in Lean is the first positive coefficient level, not the zero ring;
ramification e>1 retains e*(n+1), with no flatness assumption on any quotient;
empty X or Y is not excluded; zero input complexes are allowed in the full purity-map
agreement. Scheme/site universes are the existing `Scheme.{u}` small-site convention,
with coefficient lift `ULift.{u+1}` and sheaves of `ModuleCat.{u+1}`; no universe equality
or nonemptiness hypothesis is added. The arbitrary finite extension in the quotient
statement is not restricted to a prime-field coefficient ring.

Searches: `msearch.py` leanfinder query 'Finite diagonal smooth purity orientation at the
coefficient unit is the purity map and commutes with reduction of finite coefficient
rings' returned eight standard-smooth-algebra results, no match. Loogle query
'AlgebraicGeometry.Etale.FiniteSmoothPurity.proGamma,
AlgebraicGeometry.ProEtale.reductionCompatibilities_purity' returned zero hits (first
identifier unknown to its Mathlib index). Mathlib grep
'orientation.*reduction|purity.*coefficient' in CategoryTheory returned zero hits.
Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
`theta.*unit|Theta.*[Uu]nit|proGamma.*[Uu]nit|gamma.*[Uu]nit` found the canonical maps and
proof references, including the consumer `SmoothPurityTowerGamma`, but no declaration
stating this node's collection of identities. Further local searches of the coefficient,
finite-ring, diagonal, and tower modules established that all required constructions
already have owning dependency declarations. No new definition nodes or dependency
repairs were necessary. There is no STATEMENT-DISPUTED flag or source-based correction.

## Second reading by Q08

A fresh source-to-signature reading checked the current blueprint gamma proof (1)--(3),
the node and its six proof steps against the delivered module. In particular it checked
n+1 indexing, the unit factor in the ideal equality, the direction of the inverse
orientation, the ordering of composition, the two distinct orientation normalizations,
the scalar/root formulas in the Tate comparison, and retention of actual tower reductions.
The first draft only exposed unit normalization in ordinary-etale coordinates. The
revision adds `canonical_purity_at_unit`, whose final factor is the recorded canonical
`diagonalDualizingObject.inv` and whose left side is the recorded pro-etale purity map.
The general-ring agreement was also checked on general allowed K, not merely the unit;
`uniformizer_purity_agreement` explicitly retains that clause. All theorem proofs remain
`sorry`; every helper definition is fully constructed. This is a worker self-check under
the dispatcher instruction not to start other agents; the maintainer supplies the
independent review of the delivered statements.
