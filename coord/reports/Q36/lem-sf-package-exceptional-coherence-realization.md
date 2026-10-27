## Worker report

Q36 records `WeilConjectures.sfPackageExceptionalCoherenceRealization` in
`Sheaf.Paper.SfPackageExceptionalCoherenceRealization`. The sole postponed proof is
this named theorem, with the nine-step proof from the DAG expanded in its docstring.
Every helper predicate has an explicit body; no new coefficient category, operation,
coefficient map, dualizing object, or arbitrary chosen functor is introduced.
The item statement and proof are unchanged. Its statement dependencies gain the
already landed owners of the concrete comparison interfaces used in its signature.

Hypotheses and clauses, read against the node:

- `D : FiniteFieldDatum`, `C : D.CoefficientDatum` supply the algebraic closure of
  the finite field, characteristic p, the prime ell, ell != p and the fixed
  coefficient closure. `E`, its Field and Padic-algebra instances and
  `FiniteDimensional` supply E/Q_ell. The valuation ring, uniformizer and quotients
  are the existing `Padic.coefficientExtension...` constructions; n and hn impose
  positive exponent. No choice of a new uniformizer is made.
- `S : SixFunctorOperationDatum D C E n hn` is the exact recorded operation datum.
  Its finite category is the bounded constructible full subcategory, and its
  `finiteTorDomain` restricts to bounded constructible finite Tor. Its higher
  categories are the recorded completed, localized and pair-category constructions.
  Integral objects retain derived completeness and the uniform interval in
  `sfIntegralConstructible`; no arbitrary tower is substituted.
- `X Y : SixFunctorSpace D` already carry finite type and quasi-compactness over k.
  The two `IsSeparated` instances impose the remaining geometric hypothesis.
  The f instances express separated finite type (locally finite type plus
  quasi-compactness). They do not impose properness or smoothness on f.
- `Nonempty (Compactification f.hom.left)` gives existence. The subsequent forall c
  includes every chosen compactification. Its open/proper factorization and
  factorization equation are fields of Compactification; `QuasiCompact c.i` is
  asserted separately. Finite type of c.Z over k is written as
  `LocallyOfFiniteType (c.g ≫ Y.obj.hom)` and `QuasiCompact` of that morphism.
- The natural-number bound and `topologicalKrullDim` inequality give finite
  nonnegative dimension. `(IsEmpty c.Z → d = 0)` expressly handles the empty case.
- `SfPackageExceptionalFormulas` uses `S.finiteVerdier`, `integralVerdier`,
  `rationalVerdier`, `commonStageVerdier`, whose definitions are RHom into the
  structural exceptional image of the coefficient unit. Their morphism action is
  retained. The arbitrary cX,cY are compactifications of the structure maps.
- Its `finiteDomain` asserts exceptional preservation of the precise finite-Tor
  domain; `finiteFormula` compares functors after that full-subcategory inclusion.
  The four formulas are D_X composed with pullback of D_Y (op/rightOp give the
  covariant order). Higher exceptional functors already have the full
  constructible codomain. `finiteClass` is the class-relative adjunction with
  its original Hom bijections, units and counits, not an ambient right adjoint.
- `integralRealization` identifies S's actual exceptional functor, after inclusion,
  with `integralExceptionalInverseImage`: the specified coherent finite-exceptional
  system followed by its total derived inverse limit. The integral pullback in
  the formula is S.higher.integral.pull, the completed construction. The
  operation datum's `integralNormalization` retains all reduction comparisons
  and their adjunction equations.
- `rationalizedAdjunction` is `RationalOperations.Conclusion`, including the
  integral-rational Hom identification, exceptional identification, scalar
  compatibility and normalized dualizing identification. S.higher.rationalization
  retains both adjunction comparison equations. Common-stage inclusion and
  transition comparisons in S.closure retain those equations too.
- `SfPackageFiniteExceptionalComparisons` expands the recorded finite exceptional
  conclusion: evaluation/trace normalization; invertibility of b; quotient cocycle;
  identity quotient; unit equation; counit equation. Here predecessor index a
  denotes exponent a+1, so all positive exponents, including 1 and equal levels,
  are covered. The actual maps are FiniteExceptional.b, q and reassoc.
- `CommonStageAdjunctionDescentConclusion` writes out the exact Hom representative, unit and
  counit formulas of common-stage descent and both evaluation descent assertions.
  Its hypotheses are compatibility of the stage comparisons and specified
  compact-support functor, not a new hypothesis on the main theorem.
- `SfPackageComparisonCoherence` assembles the concrete exchange equations,
  compactification identifications, projection laws and diamonds from the recorded
  modules. Each predicate retains its own quantified domain and admissibility
  alternatives; a domain is not enlarged to arbitrary base change for Verdier
  duality. Finite-Tor and integral Hom do not acquire site-perfectness hypotheses.
- `BasicOperationsReductionConclusion` spells out the complete conclusion of elementary
  coefficient reduction, including good-representative normalizations, tensor
  and pullback comparisons, direct/support reduction, actual adjunction mates,
  evaluation, scalar identity and tower laws, and the admissible exceptional
  comparisons. All free universe parameters are fixed explicitly at u here.
- `FiniteHomComparisonConclusion` retains both the ordinary etale and intrinsic pro-etale
  comparisons, evaluation equations and uniqueness, the finite-Tor comparison
  isomorphisms, cocycles and site-comparison square. `IntegralHomReductionConclusion` retains
  the specified tensor presentations, completeness and every transpose equation.
  `SfPackageScalarHom` retains the normalized Hom, dualizing, evaluation,
  biduality, identity and successive-extension assertions.
- `PurityFiniteReductionConclusion` includes all eight conclusions of finite
  reduction of purity: the purity map, coefficient-valued trace, unit trace,
  composition source, exceptional composition, composition coherence, base change
  and affine orientation. `SfPackageSmoothOrientation` retains the geometric
  family equations (compactification, composition and smooth base change), at
  integral, rational, common and all finite coefficient-field stages, and the
  actual root-normalized transition equation. Thus geometric-Frobenius squares
  are among the allowed base-change squares rather than arbitrary new maps.
- For the additional site-perfect pairing compatibility, the actual
  `SixFunctorDatum.finitePoincarePairing` is used. `SfPackageGeometricPairingReduction`
  explicitly composes cup, evaluation and normalized-trace comparison squares;
  the clause does not take the pairing square itself as a premise. Its component
  comparisons are governed by the preceding projection, Hom/evaluation and purity
  clauses. `SfPackagePointComparisons` retains universal K-flat normalization and
  all finite quotient tensor squares of the point functor.
  `PerfectPairingAdjointsConclusion` writes out the evaluation, adjoint and inverse-adjoint
  squares, the formula for the ordinary comparison and its inverse. It does not
  assume the ordinary comparison r invertible. The site-perfect assumption is
  confined to this geometric specialization; the formal assertion applies to
  perfect pairings in the two coefficient derived categories.
- For field Weil-equivariance the rational and common-stage operation lifts use
  `PodConstructibleMate.RationalLifts`/`CommonLifts` and their `Coherence`
  predicates. These specify the actual underlying pullback/exchange/comparison
  maps and lifted units/counits, composition, exchange, projection and duality
  equations in the fixed-pair categories. `CoefVerdierWeil.Conclusion` supplies
  duality/evaluation/biduality/exceptional maps on each separated finite-type
  finite-field model. The fixed pairs are the existing IsoAlgebra realization
  used in `sfWeilComplex`, with common finite stages for algebraically closed
  coefficients. No new Weil structure or arbitrarily rescaled lift is chosen.

Dependency declarations used (module and principal interfaces):

- `Sheaf.Paper.SixFunctorOperationDatum`: SixFunctorOperationDatum and its four
  Verdier functors and finiteTorDomain/integralFiniteTorDomain.
- `Sheaf.Paper.SfWeilSheafComplex`: sfWeilComplex and its fixed-pair coefficient
  category; `WeilConjectures.Compactification.RefinementCategory`: the existing
  Compactification.Refinement interface. Mathlib `Topology.KrullDimension`:
  topologicalKrullDim.
- `Sheaf.SixFunctors.FiniteExceptionalDomain`: ProEtale.FiniteExceptionalDomain.Conclusion.
- `Sheaf.SixFunctors.FiniteExceptional`: FormulaNormalized, dualFormulaIso, b, q,
  reassoc, selfReduction and adjunction (the full finite_exceptional conclusion).
- `Sheaf.Paper.IntegralExceptionalInverseImage`: integralExceptionalInverseImage.
- `Sheaf.SixFunctors.RationalOperations`: RationalOperations.Conclusion.
- `Sheaf.SixFunctors.CoefQbarVerdier`: CoefQbarVerdierConclusion.
- `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent`: sfPackageQbarAdjunctionMapDescent's
  exact assertion and SfQbarEvaluationDescent.
- `Sheaf.Paper.FiniteCoefficientHomChange`: finiteCoefficient_derivedHom_change's
  concrete evaluation, cocycle and site interfaces.
- `Sheaf.Paper.IntegralHomReductionModels`: IntegralHom tensor/reduction presentations
  and comparison, exactly as in integralHomReduction.
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`: DualizingDatum, Conclusion,
  IdentityConclusion and CompositionConclusion.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: all concrete comparison
  interfaces of basicOperationsCoefficientReduction.
- `Sheaf.Paper.ExchangeFunctoriality`: exchangeDatumFiniteIdentification,
  exchangeFiniteStageLaws, completed/rational/common support laws, coefficient
  and mate/naturality laws.
- `Sheaf.Paper.CompactSupportProjectionFormula`: finite and higher projection
  Laws and CompactSupportProjectionChange for all four coefficient changes.
- `Sheaf.Paper.FiniteReductionComparisons`, `FiniteSmoothPullbackExchange` and
  `FiniteReductionAffineOrientation`: actual finite purity comparison maps. The eight
  assertion clauses are owned by `PurityFiniteReductionConclusion`.
- `Sheaf.Paper.DerivedPoincarePairing`: finitePoincarePairing, its finite dual twist,
  finitePairingCup, normalized trace and SfPairingGlobalGeometry.
- `Sheaf.Paper.PointFibreDerivedTensor`: PointFibreDerivedTensorSystem,
  PointFibreDerivedTensorCanonical; its scalar interfaces give the actual derived
  quotient functor and normalized scalar tensor structure.
- `Sheaf.CategoryTheory.PerfectPairingReductionAdjoints`:
  perfectPairingDualComparison. The assertion is the owned
  `PerfectPairingAdjointsConclusion`.
- `Sheaf.Paper.SixFunctorOrientationFamily`: SfOrientationDatum;
  `Sheaf.Paper.OrientationGeometricComparisons`: SfGeometricOrientation and its
  equations; `Sheaf.Paper.SixFunctorOrientationStageCompatibility`:
  SfStageOrientationCompatible.
- `Sheaf.Paper.ConstructibleMateCoherence`: PodConstructibleMate rational/common
  Lifts and Coherence. `Sheaf.SixFunctors.CoefVerdierWeilEquivariance`:
  CoefVerdierWeil.Conclusion.

The original proof dependencies were also read: BoundaryEtaleAdjunctionRestriction,
finite-type dimension and CompactificationCategory supply geometry;
IntegralResidueTor supplies the uniform reduction interval;
ConstructibleExceptionalAdjunctionCoefficients supplies the constructive
coefficient-system adjunction. The older IntegralCoefficients ambient etale API
is a proof-only import; the statement uses the intrinsic coherent integral
realization instead. An unavailable local recorded AdmissibleVerdierExchange
module was checked with `scompile.py --source`; no assertion from it is used and
no arbitrary-base-change duality assertion was substituted.

Edge cases checked: empty X/Y and empty compactification (explicit zero bound),
identity f and choice of any compactification, positive level 1, identity quotient
and three-level cocycle, dimension zero, empty support, nonproper smooth X with
finite-field model, identity coefficient extension, ramified coefficient extension,
and common stages after enlarging both representatives. No flatness of A_m/A_n,
no ramification-divisibility assumption and no site-perfect condition on general
finite-Tor/internal-Hom objects is added. The pairing's even shift remains inside
its existing orientation line.

Searches made before writing:

- msearch.py leanfinder, `Constructible exceptional adjunction via Verdier duality
  at finite integral rational and algebraically closed coefficients with coherent
  comparison maps`: eight generic condensed/sheaf adjoints; no complete match.
- msearch.py loogle, `CategoryTheory.Adjunction`: twelve generic adjunction
  declarations; no constructible coefficient package.
- msearch.py grep, `Verdier|exceptionalInverse|sixFunctor.*[Cc]oher`: twenty-five
  unrelated Mathlib Verdier/triangulated references; no match.
- msearch.py leansearch, `six functor exceptional adjunction Verdier duality and
  coherence of coefficient comparisons`: eight generic adjoints; no match.
- rg on lean/WeilConjectures and lean/Sheaf for exceptional/coherence and
  six-functor coherence, and exact item-id search on WeilConjectures: component
  operations and comparison modules only, no declaration of the full node.
- Subsequent rg searches for pairing, finite coefficient Hom, purity and
  Frobenius comparisons found the interfaces cited above. The upstream
  PoincareReduction theorem is only the formal implication from a pairing
  square; it is not recorded as an existing statement of this whole node.

Ten new definition nodes are delivered in this repair: nine own existing interfaces
and one owns the seven named conclusion predicates in a separate definition module.
No dependency replacement module or statement correction is needed.

## Second reading by Q36

The dispatcher's brief forbids starting another agent and specifies the
maintainer's independent delivery review. This section records my own second
reading; it does not claim an independent worker review.

The second reading made the finite class-relative domain explicit, retained the
actual integral total-limit realization, expanded finite quotient identity and
cocycle and both adjunction equations, removed implicit universes, and added the
complete elementary coefficient comparison conclusion. It kept general Hom
separate from the additional site-perfect pairing domain, added the actual
geometric pairing composite, and retained the eight separate purity reduction
clauses and the normalized field fixed-pair comparisons. Compile warnings were
repaired by naming proof-only binders with underscore prefixes, without deleting
hypotheses. The maintainer should check the assembled pairing clauses especially:
the three component squares are asserted through the component comparison clauses,
while the geometric pairing predicate spells out their composition and the
formal predicate spells out passage to inverse adjoints. There is one named
postponed proof, and no definition has postponed data.


## Returned-head repair H2 and H4

Compared the sandbox with returned head 4308050cd158 through its retained delivered
files and with the current main node/source records. Only the item fields `lean`
and `stmt_deps` differ from main. Its natural-language statement, source, proof and
proof dependencies remain byte-for-byte the current-main values. The exceptional
conjunct accepted in the return is unchanged, including the explicit empty-case
zero dimension and all four dual formulas.

H2: removed all eleven theorem statement dependencies identified by the reviewer.
The only theorem statement dependencies retained are `lem-coef-finite-exceptional`
and `lem-coef-integral-finite-extension`: their uniquely normalized constructions
actually provide data used by the statement. The other interfaces have the nine
existing:true definition owners below. CommonLifts reuses the already landed
`def-sf-constructible-common-stage-data` instead of acquiring another owner.
Purity and integral Hom now explicitly cite `def-pur-finite-reduction-comparisons`
and `def-sf-integral-hom-reduction-models`. Purity also uses the existing definition
owners `def-pur-smooth-pullback-exchange` and
`def-pur-finite-affine-orientation-comparison` for the base-change and orientation
maps, rather than importing their final reduction theorem to expose them.

H4: removed the seven copied conclusion predicates from the item module. The new
module `Sheaf.Paper.SfCoefficientComparisonConclusions` owns their named predicates
once. The main coherence predicate applies these names. The integral-Hom clause
inside `BasicOperationsReductionConclusion` now uses
`IntegralHomReductionConclusion l E W D hl`, rather than repeating its body.
The seven predicates have real Prop bodies and introduce no chosen map or proof.
This is a definition-module extraction requested by the return, not another proof
of the source theorems. There remains exactly one sorry, in the item theorem.
The advisory about universally quantified law predicates is recorded: these retain
the previously reviewed domains, while the item applies the applicable coefficient
predicates to its own D,C,E. No hypothesis on S has been added.

Repair searches: msearch.py leansearch queried canonical finite Hom evaluation,
quotient/site comparison, integral Hom, purity, pairing adjoints, common-stage
adjunction descent and basic-operation coherence. Eight hits were generic Hom
complex cocycles, with no relevant interface. The leanfinder query for exceptional
domains, canonical point tensor, exchange/projection and rational/common-stage
coherence returned generic monoidal, condensed and internally-projective interfaces.
Mathlib grep for the exact interface names returned zero hits. These raw result
records are preserved in every new node's mathlib_searches. rg in WeilConjectures
found none of the exact names; rg in Sheaf found precisely the published definitions
in the owning modules below. Exact DAG declaration searches found theorem records
for the unowned definitions, and the existing CommonLifts owner noted above.
`blueprint_refs.py search coefficient coherence` returned 33 related blueprint nodes;
none owns these new interface predicates. The new seven conclusion names had no
hits in Mathlib, WeilConjectures, Sheaf or the DAG before extraction.

Both delivered modules compiled cleanly with scompile.py in dependency order on
2026-10-24. The first compile identified the two direct purity interface imports;
adding those existing definition modules resolved every error. The final compile
reported no errors or warnings.

## New nodes

`def-sf-basic-operation-coefficient-laws`: Elementary coefficient comparison law predicates. Reuses `WeilConjectures.coefficientOperationMateEquations` and the listed plain interfaces in `Sheaf.Paper.BasicOperationsCoefficientReduction` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-coefficient-comparison-conclusions`: Named coefficient, purity and pairing conclusions. Owns the seven named conclusion predicates in `Sheaf.Paper.SfCoefficientComparisonConclusions`; each complete domain and every equation is retained, with integral Hom factored once. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-common-stage-evaluation-descent`: Common-stage evaluation descent assertion. Reuses `WeilConjectures.SfQbarEvaluationDescent` and the listed plain interfaces in `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-constructible-mate-coherence-predicates`: Rational and common-field Weil comparison coherence. Reuses `WeilConjectures.PodConstructibleMate.RationalCoherence` and the listed plain interfaces in `Sheaf.Paper.ConstructibleMateCoherence` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-exchange-coherence-laws`: Canonical exchange and coefficient law predicates. Reuses `WeilConjectures.exchangeFiniteStageLaws` and the listed plain interfaces in `Sheaf.Paper.ExchangeFunctoriality` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-finite-exceptional-restriction-conclusion`: Finite exceptional restriction assertion. Reuses `AlgebraicGeometry.ProEtale.FiniteExceptionalDomain.Conclusion` and the listed plain interfaces in `Sheaf.SixFunctors.FiniteExceptionalDomain` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-finite-hom-comparison-equations`: Finite coefficient Hom evaluation and cocycle predicates. Reuses `WeilConjectures.FiniteHomEvaluation` and the listed plain interfaces in `Sheaf.Paper.FiniteCoefficientHomChange` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-perfect-pairing-dual-comparison`: Specified dual comparison of a perfect pairing. Reuses `CategoryTheory.perfectPairingDualComparison` and the listed plain interfaces in `Sheaf.CategoryTheory.PerfectPairingReductionAdjoints` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-point-fibre-tensor-canonical-system`: Canonical simultaneous point-fibre tensor normalization. Reuses `WeilConjectures.PointFibreDerivedTensorCanonical` and the listed plain interfaces in `Sheaf.Paper.PointFibreDerivedTensor` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

`def-sf-projection-coefficient-square`: Canonical projection coefficient-change equation. Reuses `WeilConjectures.CompactSupportProjectionChange` and the listed plain interfaces in `Sheaf.Paper.CompactSupportProjectionFormula` without copying or moving code. The source is the current package proof's exceptional/coherence sentences and the component comparison definitions they invoke. The common searches above found no existing DAG owner for these declarations; this node supplies ownership, not a duplicate construction.

## Repair second reading by Q36

Read each of the ten new node statements alongside its defining signature/body,
and reread the item coherence predicate and its main theorem. The finite domain
node is in `AlgebraicGeometry.ProEtale.FiniteExceptionalDomain`, rather than
WeilConjectures; its full namespace was corrected in the record. The finite Hom
predicate retains both sites, both evaluation clauses and uniqueness, Tor-domain
preservation/isomorphisms, cocycles and site square. Integral Hom retains all
presentation, completeness, evaluation and transpose quantifiers. Purity retains
eight clauses and their separate smooth and finite-Tor hypotheses. Common descent
retains coherent unit/counit premises, both Hom representative formulas, unit,
counit and evaluation. Pairing retains its two normalized pairings and the
explicit inverse without assuming r invertible. Basic operations retains every
old conjunct; only its repeated integral-Hom expansion is now a predicate call.
Projection retains all four coefficient squares, including ramified finite change.
All new interface nodes are definitional records, not theorem dependencies in
disguise: none asserts that its laws hold. Empty schemes, positive level 1, equal
quotients, identity and third-field coefficient extensions are still quantified.
No independent agent was started, in accordance with the dispatch brief.
