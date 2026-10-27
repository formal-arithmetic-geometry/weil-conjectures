## Worker report

The module `lean/Sheaf/Paper/NormalizedOrientationPerfectDuality.lean` states
`WeilConjectures.sfPackageNormalizedOrientationPerfectDuality`, with one `sorry`.
Its eight conjuncts use explicit Prop-valued definitions of this node's clauses.
Their bodies are complete logical formulas; no definition contains postponed data.
`sfPackageCommonStagePurity` is the existing `smallModelIso` with its finite-stage
source and target made explicit. It does not choose an endpoint isomorphism.

Source read: current main-20261015,
`sec-six-functors/sk-thm-sf-package/prop-functor-package.proof.md`, clause (6) and
the point/site-perfect sentence of (7), together with the item's full statement
and proof. The statement has not been corrected. The additional statement edges
are already recorded definition nodes owning interfaces used in the formula.
The repair adds one definition node for the existing perfect-evaluation maps;
there are no dependency modules or statement corrections.

### Hypotheses and clauses

* The finite-field and coefficient hypotheses are `FiniteFieldDatum.{u}` and its
  `CoefficientDatum`; `PurityFiniteSetting.{u}` includes the finite extension
  inside its fixed algebraic closure, positive exponent, and the actual finite
  coefficient ring. The smooth specialization uses `SixFunctorOperationDatum`,
  not `SixFunctorDatum`. Coefficient integers, uniformizer ideals and quotient
  rings are the recorded `Padic.coefficientExtension*` constructions.
* Schemes carry their `Over (Spec k)` structures, `LocallyOfFiniteType`,
  `QuasiCompact` and `IsSeparated` over k. Morphisms are over k and have all
  three corresponding separated finite-type instances. Pure relative dimension
  is `d : ℕ` and `SmoothOfRelativeDimension d f`, including dimension zero.
* Finite inputs use `finiteTorConstructible`. Integral inputs use
  `sfIntegralConstructible`, whose definition includes derived completeness and
  one cohomological interval for all reductions. `SfPackageIntegralOrientation`
  asserts their uniform finite-Tor membership, rather than requiring it as an
  added hypothesis. The field inputs are the actual scalar-localized and common
  finite-field-stage constructible categories.
* `SfPackageFiniteOrientationTrace` gives an iso whose hom is exactly
  `P.smoothPurityMap f d K hK`. Its inverse is therefore the requested reverse
  comparison. The trace is `smoothCompactSupport.map e.hom` followed by
  `smoothExceptionalCounit`. For every `1 ≤ m ≤ P.level`, all three equations
  are written with the actual reduction functor, source comparison, exceptional
  comparison, and support comparison. No quotient-flatness assumption is used.
* `SfPackageIntegralOrientation` retains the strict coefficient-system witness
  `G`, its evaluation identities, and the equation expressing the forward map
  as the completion unit followed by the total limit of `G`. At each exponent
  `n+1`, it gives the prescribed `purAdicSourceReduction` and
  `purAdicTargetReduction`, their invertibility, the forward reduction square,
  and the inverse square with the inverse of that very finite purity map.
  It makes no uniqueness assertion about a general coherent lift.
* `SfPackageIntegralOrientationTrace` now quantifies one `eR` together with
  `SfPackageIntegralReconstruction ... eR`, including its strict tower witness,
  actual completion-unit formula and forward/inverse finite reduction squares.
  The source and target realization isomorphisms `s,b` identify this same `eR`
  with the actual lattice `integralMap`: `s.hom ≫ integralMap.hom = eR.hom ≫ b.hom`.
  The target realization is normalized at every exponent by
  `SfPackageIntegralCounitReduction`. Its map is the literal
  `sfPackageReconstructedIntegralCounit`, formed from support of `b`, the actual
  support realization and actual exceptional counit. Its reduction is the canonical
  support comparison, finite support realization, support of
  `purAdicTargetReduction`, and the **actual finite exceptional counit**. This is
  the scalar-adjoint normalization of the exceptional comparison; it does not
  supply an unconstrained arrow between the endpoints.
* `sfPackageReconstructedIntegralTrace` is defined by support of `eR.hom`,
  support of `b.hom`, the inverse actual support realization and the actual
  exceptional counit. `SfPackageIntegralOrientationTrace` identifies it with
  support of `s.hom` followed by the lattice counit trace. Its final conjunct is
  `SfPackageIntegralTraceReduction` for **that very constructed trace**, at every
  integral input `K` and every exponent `n+1`. The equality reads
  `Q_Y.map t = supportComparison ≫ finiteSupportRealization ≫ P_n.map a_K ≫ t_n`,
  where `a_K` is literally `purAdicSourceReduction` and `t_n` is literally
  `coefficientValuedSmoothTrace` on `Q_Y K`, with the existing finite-Tor witness.
  Each finite level also satisfies `SfPackageFiniteOrientationTrace`, retaining
  the forward, inverse and trace equations for every `1 ≤ m ≤ n+1`, with the
  actual further-quotient support/source/exceptional comparisons and counits.
  The fixed compactification is the existing `integralExceptionalCompactification`;
  changing its presentation is not an extra hypothesis on the geometric input.
* `SfPackageRationalOrientationTrace` pins the inverse to `rationalIso.symm`.
  That definition rationalizes `integralIso` on `representative P K` and uses
  `rationalSourceComparison`, the exceptional comparison, and
  `representative_eq`. The trace equation retains the same lattice, the support
  comparison and the final representative identification.
* `SfPackageFieldOrientationTrace` writes all three equations for every actual
  finite coefficient embedding: forward purity, inverse purity, and trace.
  It uses `sourceScalar` and the counit-preserving `rationalComparison`.
* `SfPackageCommonOrientation` pins the inverse to `commonIso` and writes its
  counit trace through `commonSourceComparison`, the literal `K.stage`, its
  fixed field-model purity, and `S.common.commonComparison`. Identity and
  composite comparisons are retained by those recorded stage-system and
  coefficient-system constructions. No field-to-finite-quotient functor occurs.
* `SfPackagePointEvaluation` uses ordinary `Module.Dual.eval` for finite modules
  over the positive finite quotient. At the valuation ring and both field
  stages it uses `boundedFiniteCoefficientComplex` and the actual derived
  `coefficientDerivedEvaluation` into the coefficient unit. The module derived
  localizations are explicit `HasDerivedCategory.{u}` construction data, as in
  the dependency's API; they are not mathematical duality assumptions.
* `SfPackageSmoothSitePerfect` takes only the operation datum. It asserts
  existence of closed presentations with `SixFunctorAmbientClosedModel`
  normalization at finite and completed coefficients, and
  `SixFunctorClosedChange` at rational and common coefficients. These retain
  internal-Hom identity coordinates, tensor, evaluation and signed symmetry.
  Membership of the line and omega in the displayed domains is a conclusion.
  Omega is literally the operation datum's exceptional image of its coefficient
  unit. Orientation isos are asserted to exist; the evaluation calculation is
  stated under each such iso, so in particular under the specified purity iso.
  No data is defined by choosing one of those existence assertions.
* The four site-perfect predicates are the recorded finite, integral, rational
  and general common-stage ones. `SfPackagePerfectEvaluation` spells out the
  theta iso with inverse exactly `sfPerfectThetaInverse`, and the cancellation
  iso with hom exactly `sfPerfectLineCancellation`. Its displayed equality
  identifies the actual `ringedSiteBidual` with coefficient-unit biduality;
  both are explicitly invertible. It does not replace either arrow by an
  arbitrary map or by equality of cohomology dimensions.

### Dependency declarations used

* `Sheaf.Paper.SixFunctorOperationDatum`: `SixFunctorOperationDatum`, its
  finite/integral domains and actual finite/integral/rational/common dualizing
  objects; `SixFunctorSpace` and `sixFunctorStructure` from its recorded stages.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `sfQbarTwistingCoefficient` and the recorded signed coefficient-line convention.
* `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap`.
* `Sheaf.Paper.SmoothTrace`: `smoothCompactSupport`, `smoothExceptionalCounit`,
  `coefficientValuedSmoothTrace`.
* `Sheaf.Paper.SitePerfectComplex`: `IsFiniteCoefficientSitePerfect`,
  `IsIntegralCoefficientSitePerfect`, `IsSfRationalCoefficientSitePerfect`,
  `IsGeneralAlgebraicallyClosedCoefficientSitePerfect`.
* `Sheaf.Paper.PurAdicReconstruction`: `purAdicReconstruction` and
  `purAdicRestrictedEvaluation`, with its source/target reduction interfaces.
* `Sheaf.Paper.RationalSmoothPurityCanonical`: `integralMap`, `integralIso`,
  `integralTraceTranspose`, `IsNormalizedTrace`, `orientation`, `orientationTrace`,
  `rationalIso`, `representative`, `representative_eq`, `rationalSourceComparison`,
  `rationalIso_scalar`, `smallModelIso`, `commonIso`, and `stageSetting`.
  Its public source-transports module supplies `sourceScalar`, `rationalSource`,
  `commonSource`, and `commonSourceComparison`.
* `Sheaf.Paper.CoefficientDuality`: `boundedFiniteCoefficientComplex` and
  `coefficientDerivedEvaluation`.
* Added recorded definitions: `Sheaf.Paper.SixFunctorDatum` supplies
  `SixFunctorClosedDomain`, `SixFunctorAmbientClosedModel`,
  `SixFunctorCoefficientClosedModels`, `SixFunctorClosedChange` and
  `sixFunctorRingedModel`; `Sheaf.Paper.OrientationCoefficientTwists` supplies
  `sfOrientationIntegralLineOn`; `Sheaf.Paper.SixFunctorOrientationFiniteFamily`
  supplies `sfOrientationReducedLine`; the recorded `FiniteReductionRootCharts`
  and `FiniteReductionComparisons` modules supply the finite reduction functor
  and its canonical source, support and exceptional comparisons.
* `Sheaf.Paper.OrientedPerfectDuality`: `sfPerfectThetaInverse` and
  `sfPerfectLineCancellation`, now owned by the new definition node
  `def-sf-perfect-evaluation-comparisons` in `stmt_deps`. Its full theorem requires a `SixFunctorDatum`
  containing A6. I deliberately did not add that as a hypothesis: the present
  package states the independent local perfect-evaluation calculation directly.
* Proof-plan imports: `FiniteCoefficientSmoothPurity`, `FiniteReductionOfPurity`,
  `CoefficientFrobenius`, `IntegralResidueTor`, and `SitePerfectCoefficientDual`.
  Their relevant declarations are `isIso_smoothPurityMap`, finite purity/trace
  reduction, `coefficient_frobenius`, `integral_coefficient_derived_duality`,
  `integral_residue_tor`, and the local coefficient-perfect evaluation results.

### Edge cases

Checked the formulas and domains at exponent 1 (tower index 0), equal finite
quotients, identical coefficient fields, identity morphisms, dimension 0, the
zero complex, the empty scheme, and integral torsion modules. The finite inverse
has no instance-selection ambiguity: the iso is pinned by its hom. Empty schemes
are not excluded by nonemptiness or connectedness hypotheses. Bounds are uniform
in the integral tower. Integral torsion uses derived Hom: ordinary duality of
`R/(varpi)` would give zero and is not claimed. Site-perfectness remains a local
finite-projective condition and is never equated with finite Tor amplitude.
All universes and variables are explicitly bound; the module disables both forms
of auto-implicit variables. No general geometric biduality is assumed.

### Searches

Ran the prescribed `msearch.py Q76 <item>` searches (raw records in the sandbox's
`searches.jsonl`):

* leanfinder: "Normalized smooth purity inverse orientation and perfect complex
  evaluation biduality for finite integral rational coefficient sheaves" — eight
  unrelated scheme-normalization results, no match.
* loogle: `"purity", "Iso"` — zero hits.
* grep, Mathlib `CategoryTheory`: `smoothPurity|purityIso|verdierDual` — zero hits.
* leansearch: "Smooth purity trace and perfect sheaf complex evaluation biduality
  over integral and field coefficients" — eight ordinary linear-algebra dual/trace
  results, no match.

Searched the project's `lean/WeilConjectures` and `lean/Sheaf` with rg for smooth
purity, orientation, trace and perfect biduality and read the existing constituent
interfaces. The upstream perfect-duality result and the newly recorded relative
one do not state the whole package. The latter also has the stronger full-datum
hypothesis explained above. The exact item-id grep in `lean/WeilConjectures`
returned no declaration. All newly declared names were searched in Mathlib,
`lean/WeilConjectures` and `lean/Sheaf`; no collisions were found.

### Validation

All compiles use `scompile.py`; the shared source and published library remain
read-only. No compile limit was raised. The repaired general-input trace and
counit squares have compiled on the server; the final validation results follow
below after preflight. The only postponed proof remains the item's named theorem.

## Repair of returned head 6aaff388e614

1. The returned integral trace was attached only to `integralMap`, with unit-only
   normalization and no relation to the reconstruction witness. The repaired
   statement shares the reconstruction predicate and its witness `eR` inside
   `SfPackageIntegralOrientationTrace`. It states the map-identification equation,
   normalizes its target realization by the actual exceptional counit reduction square, defines
   the counit trace directly from `eR`, identifies it with the lattice trace, and
   states its **general-input** finite reduction equation. This is the third display
   of `lem-sf-normalized-integral-purity-trace`, in the published support/source
   coordinates. Every finite-stage trace retains all further quotient equations.
   No faithfulness or uniqueness of arbitrary lifts from reductions is claimed.
2. The two perfect-evaluation maps were recorded only on a theorem node. The new
   existing-definition node records exactly their published signatures and complete
   evaluation-transpose constructions; the item cites it. There is no duplicate
   Lean definition and no added `SixFunctorDatum` or general-biduality hypothesis.

## New nodes

`def-sf-perfect-evaluation-comparisons` records `sfPerfectThetaInverse` and
`sfPerfectLineCancellation`, already defined in
`Sheaf.Paper.OrientedPerfectDuality` at lines 42 and 52, with `existing: true`.
The source is the evaluation compatibility and double-dual cancellation of
`sk-thm-sf-dual-perfect/thm-sf-dual-perfect.proof.md`, Steps 3–5, used in the
package proof's smooth site-perfect clause (7). Its TeX gives both actual
transpose formulas, with no claim of their invertibility and no perfectness
hypothesis. Its only prerequisite notion is the existing closed tensor-Hom
structure of `def-coef-ringed-tensor-hom-model`.

The three prescribed Mathlib searches were rerun: LeanSearch found monoidal
inverse/unit identities; LeanFinder found tensor duality contractions;
grep of CategoryTheory for the exact names and `ringedSiteDualEvaluation` found
no match. The raw records are in `searches.jsonl` and copied into the new node.
The project/DAG search found these maps only in the existing theorem module
and its theorem node; there is no definition node carrying them. The blueprint `theta` search returned 99 matches, including the oriented
perfect-duality unit as the relevant hit; the exact declaration-name search
found only the existing theorem owner. This node therefore records existing definitions, rather
than introducing a second notion.

### Repair self-check

Compared the retained packet with the current shared node: only the authorized
`lean` and added definition dependencies differ. The TeX statement, proof plan,
source and other fields remain unchanged. Read the current source signatures
of the actual scalar/exceptional/support comparisons used by the repair. The
trace equality has the same raw-source domain on both sides; its target is
`Q_Y K`, not the coefficient unit. Level zero means exponent one; the same-level
quotient is included. The zero complex, dimension zero, empty scheme and
integral torsion inputs still have the original domains. All new definitions
are explicit composites or complete propositions. The only postponed proof
remains the item's named theorem.

The direct expansion of the restricted exceptional scalar mate exceeded the file's
60-second limit. It was replaced by its equivalent defining counit square:
`SfPackageIntegralCounitReduction`. The canonical support comparison and actual
finite exceptional counit are retained verbatim, so the normalization is unchanged;
no compile limit was raised.

Final repaired module compile: `scompile.py` passed with no errors or unexpected
warnings, both as `Sheaf.Stage2.Sandbox0` (36.1 s) and as the actual
`Sheaf.Paper.NormalizedOrientationPerfectDuality` module (36.8 s). Local
irreducibility annotations keep the already typed adic source/target and lattice
source from being repeatedly unfolded; the reconstruction formula is elaborated
before making its target locally irreducible. These annotations change no map,
statement or definition data. The profiling option appeared only in a scratch
probe and is absent from the delivered module.

## Second reading by Q76

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
