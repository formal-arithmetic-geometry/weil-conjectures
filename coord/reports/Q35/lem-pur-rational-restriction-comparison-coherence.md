## Worker report

The module `Sheaf.Paper.RationalRestrictionComparisonCoherence` states all clauses
of `lem-pur-rational-restriction-comparison-coherence` in namespace
`WeilConjectures.RationalRestrictionComparison`. Every theorem has proof `sorry`.
Aliases have explicit functor/comparison result types to avoid repeated unfolding.
Their bodies are exactly the recorded constructions. Other definitions choose
an object uniquely determined by the
component equations of the immediately preceding existence-and-uniqueness theorem.
No dependency repair or new definition node is needed.

The source read is the current blueprint's
`sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md`, final
invertibility assertion, and the rational paragraph of the current DAG's
`def-weil-derived-pullback-tensor-hom`. As the assigned node itself records, this
is an agent subargument for finite-clopen transport; the blueprint only asserts
invertibility. The eight proof steps of the node are rendered in the theorem
docstrings, including the balancing calculation and recursive equation argument.

Hypothesis and clause correspondence:

- `P : PurityFiniteSetting` contains the fixed algebraic closure of the finite
  field, prime ell different from its characteristic, and fixed closure Qbar of
  Q_ell. Its finite-level extension and positive level are irrelevant to these
  operations; no condition is placed on them. Every permitted global datum
  admits such settings, and the result is uniform in this unused finite data.
- `Schemes P` is `Over (Spec (CommRingCat.of P.field.k))`. Thus `f : Y ⟶ X`
  is an actual morphism over k, with its commuting triangle. `hXft`, `hXqc`,
  `hYft`, `hYqc` require the two structure maps to be locally of finite type and
  quasi-compact, exactly finite type. They are explicitly retained in
  `mixedSquares`. No smoothness, properness or separation is assumed.
- `Fields P` is the recorded `AlgebraicallyClosedCoefficients.Index`, namely
  all finite intermediate subfields of the fixed closure. `FieldAt` is the actual intermediate field `E.val`, with its inherited
  field and finite-dimensional algebra structures. `E`, `L`, `F`, `h : E ≤ L`, `j : L ≤ F` quantify over every
  field and inclusion; equality and repeated stages are allowed.
- `integralCategory`, `rationalCategory`, and `localization` are the recorded
  intrinsic constructible categories and unchanged-object raw localization.
  They use the small pro-etale site (object universe u+1, morphisms u),
  completed integral coefficients, derived completeness, and bounded
  constructible reductions. There is no Karoubi completion.
- `integralPullback`, `integralTensor`, `rationalPullback`, `rationalTensor`
  are definitions with explicit functor types, whose bodies are aliases for the recorded restrictions and rational extensions of the
  completed operations. Their codomains express closure in constructibles.
  `linear` retains O_E-linearity for every field. `residueInvertible`
  constructs prime invertibility from `P.coefficientPrime_isUnit_stalk`,
  mapping the resulting unit to the residue field; it is not a hypothesis.
- `integralScalar` and `rationalScalar` are the specified completed scalar
  extension and its rationalization along `IntermediateField.inclusion`. The inherited
  proof-only characteristic parameter is 0, as in the operation-comparison
  API; primality supplies ell nonzero. It changes no operation.
- `integralB`, `integralTheta` are exactly `integralPullbackScalarComparison`
  and `integralTensorScalarComparison`, using the canonical normalized
  `scalarPullbackCompleted` and `scalarTensorCompleted`, respectively.
  `rationalB`, `rationalTheta` reuse their unique recorded rational extensions.
- `integralUnit` is `constantWeilIntegralObject`, the regular completed
  coefficient object. `integralUpsilon` and `rationalUpsilon` are the specified
  canonical scalar-unit maps from `ConstantCoefficientScalarNormalization`.
- `μ` is the family of natural integral tensor isomorphisms of the node;
  `ε` is its family of integral unit isomorphisms. `hTensor`, `hUnit` are
  exactly its two displayed integral mixed equations, written with Lean's
  left-to-right composition. Their endpoints use the very same canonical b,
  theta and upsilon, and both tensor inputs occur.
- `tensorComparison_existsUnique` asserts the natural rational isomorphism
  with hom AND inverse components exactly Q of those of μ. `tensorComparison`
  chooses that unique isomorphism. `unitComparison_existsUnique` and
  `unitComparison` do the same for ε. This postpones only the proof of their
  normalized existence, not arbitrary unspecified data.
- `scalarComparisons_localized` states that b, theta and upsilon, and each
  inverse, are exactly the localized integral arrows, component by component.
  Their existing types supply natural isomorphisms on every rational arrow.
- `mixedSquares` concludes both displayed rational mixed-square equations,
  for every inclusion and all rational objects. Its rational μ and ε are
  the uniquely normalized ones, not existential witnesses with unspecified
  components. No injectivity of integral Hom into rational Hom is assumed.
- `identityCoherence` states the identity b and theta equations with
  `rationalUnitor`. `towerCoherence` states both tower equations with
  `rationalAssociator`. These are aliases of the existing `sfRationalScalarUnit` and
  `sfRationalScalarComp`, fixed by the localized integral scalar unit and
  associator. Composed/self subtype inclusions identify definitionally with
  the direct/identity inclusion, including repeated fields.
- `pureArrowActions` gives pullback additivity and its pure-arrow formula.
  The tensor clause supplies an actual bilinear Hom map agreeing with the
  rational tensor functor and multiplying the two coefficients on pure arrows.
  Thus balancing and additive extension in both variables are explicit.
  Scalar-first `Localization.Away varpi` coordinates are the recorded model;
  `sfRationalCoefficientEquiv` canonically identifies them with the source's
  Hom-first E coordinates. All coefficients are covered by this equivalence.
- `equationCalculus` gives equality, identity and composition preservation
  by Q and commuting laws for pullback, scalar extension and tensor. Together
  with the comparison/inverse prescriptions these are the recursive evaluation
  laws for every finite well-typed integral comparison expression: induction
  identifies its rational evaluation with Q of its integral evaluation.
  Consequently every specified integral equality remains an equality.

Recorded dependency declarations used (signatures and docstrings read):

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`,
  `PurityFiniteSetting.coefficientPrime_isUnit_stalk`; underlying
  `FiniteFieldDatum`, `FiniteFieldDatum.CoefficientDatum`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`; the site is
  inherited through the intrinsic coefficient categories.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `IntegralOnSlice.completedTensor` and the publicly retained global operations.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`, inherited through constructible extension.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarPullbackCompleted`, `scalarTensorCompleted`,
  `scalarOperationsOrdinary_tower` (proof import retained).
- `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralScalarComp`,
  `sfIntegralScalarUnit`, `sfRationalScalarComp`, `sfRationalScalarUnit` and
  their localized component normalization interfaces.
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`:
  `constantCoefficientConstructibleScalarIso`, `constantCoefficientRationalScalarIso`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `constructibleIntegralTensor`, `rationalDerivedPullback`, `rationalDerivedTensor`,
  the integral/rational pullback and tensor scalar comparisons.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization.localization`;
  `Sheaf.CategoryTheory.SemilinearScalarLocalization`: semilinear extension and
  natural-isomorphism specifications (proof import).
- Added landed statement dependency `def-weil-algebraically-closed-coefficients`:
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` publicly supplies the
  existing finite-field `Index`. Actual coefficient carriers are used here,
  so no Shrink transport or additional coefficient universe is required.
  Its full statement/proof
  dependency traversal found no path back to this item (3196 visited nodes).

Edge cases: E=L and E=L=F retain the specified unit/associator, never a false
strict identity of chosen completed functors. Empty schemes, zero objects and
torsion maps killed by localization are included. No nonempty index, finite
Tor-amplitude or Hom-injectivity premise is introduced. Both tensor variables
are covariant, and the coefficient product is taken in the target field.

Reuse searches:

- LeanFinder via msearch: “Rationalized natural tensor pullback comparisons
  preserve coefficient extension mixed squares and tower coherence”: eight
  ordinary base-change/polynomial-law hits, none giving the statement.
- Loogle via msearch: `CategoryTheory.Functor.mapIso,
  CategoryTheory.NatIso.ofComponents`: no combined match.
- Mathlib grep via msearch: `rational.*comparison|comparison.*rational`
  in CategoryTheory: no hits.
- Earlier logged LeanSearch query “Rationalization of linear categories preserves
  natural isomorphisms and bilinear comparison equations”: eight generic free
  category/product comparison/linear functor hits, no completed-operation match.
- Source rg in both WeilConjectures and Sheaf for rational mixed equations and
  declaration names located adjacent realization/point-transport interfaces,
  none this statement. Exact item-id grep in WeilConjectures found no match.
  Existing rational operations and normalized scalar comparisons are reused.

No mathematical statement correction, disputed statement, independent new
notion or dependency repair is required. Only `lean` and the addition of the
already-landed coefficient-definition dependency change in the node copy.

Validation uses only the prescribed single-file scompile wrapper, followed by
`deliver2.py --no-push` and then delivery. Initial checks exposed an empty-line
linter warning and excessive unfolding while elaborating the complete clauses;
those are repaired in the final module before delivery. Profiling identified
repeated structure comparisons on Shrink models as the bottleneck. Using the
actual intermediate fields in the already fixed coefficient universe removes
that unnecessary size transport without restricting any field or morphism.
Explicit functor/comparison result types then avoid recomputing large inferred
endpoints during compositions; their bodies remain exactly the existing maps.
The resulting complete module passed both sandbox and library checks without
warnings before the final delivery dry run.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
