## Worker report

The delivery states `WeilConjectures.VerdierExchange.verdier_exchange` in
`Sheaf.Paper.VerdierExchange`. Its proof is `sorry`; all helper definitions have
real data. The statement uses the existing coefficient categories and the
unconditional constructible exceptional adjunctions, rather than assuming an
ambient exceptional right adjoint. The helper records are conclusion data in
`Nonempty Package`, not hypotheses supplied to the theorem.

The source is the current blueprint main-20261015,
`sec-six-functors/sk-thm-sf-verdier-exchange/_section.md` and its proof. The
resolved stage-1 repair note requests the split coefficient-mate proof route;
the theorem docstring follows the resulting eight proof steps and names their
separate dependencies. No statement correction is made.

Hypotheses and clauses:

* The global datum is `D : FiniteFieldDatum`, `l : ℕ`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`, and `Ω` with field, Padic algebra and algebraic-closure
  instances. `System` uses that same datum. The finite extension carriers and
  their Padic algebras are the existing `FieldStage`, not new coefficient rings.
* `X` and `Y` are schemes over `Spec (.of D.k)`. Each structure morphism has
  `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`. The last two express
  finite type. The corresponding three instances on `f`, and `f.IsOver`, express
  exactly the separated finite-type k-morphism in the node.
* `Assertion` specializes `Package` to `Z = Spec k`, `g = a_Y`, and the third
  morphism `f ≫ a_Y = a_X`. Its local self-over instance is identity, to avoid
  confusing it with the non-definitionally identical `Spec.map id`. It
  quantifies over choices of the published normalized Systems and over
  compactifications; it makes no ambient-adjoint assumption.
* `Package.unit s` is the coefficient at the point. At ring stages
  `RingRealization.unitIso` identifies it with the actual coefficient module
  placed in degree zero by `ringUnit`. Its coefficient identification is fixed
  by `ringUnitScalar`, the transpose of the actual restriction-unit module map.
  Rationalization and common-stage `StageScalar.unit` identify the other units.
* `A.G.obj unit` and `B.G.obj unit` in `StageData` are omega_Y and omega_X.
  `StageData.dualY` and `.dualX` are contravariant internal Hom into those
  objects. At finite and integral coefficients `RingRealization.homX/homY`
  identify them with `derivedInternalHomOfUniverses` on the original small
  pro-etale sites. Evaluation is normalized by `evaluationX/evaluationY` and
  the signed K-flat `RingedSiteDualityModel`, not by arbitrary bilinear maps.
* `StageData.dualizing` is the displayed isomorphism `Rf^! omega_Y ≅ omega_X`.
  `Package.integralAlpha_normalized` identifies the compositor with the actual
  completed proper/open compositor `sfFieldShriekCompositionIntegral`.
  `integralDualizing` fixes its right-adjoint conjugate, evaluated at the unit.
  `ScalarConclusion.dualizing` is its finite-reduction/scalar square. Together
  these specify the finite and field forms of the same comparison.
* `StageData.epsilon` is a real arrow: projection followed by evaluation,
  exceptional-adjunction transposition, postcomposition with the dualizing
  comparison, closed transposition, and the ordinary pull/star adjunction.
  This is the inverse tensor-Hom exchange followed by `Rf_* RHom(M,c)`;
  helpers `exchange` and `substitute` also spell out that orientation directly.
  `StageConclusion.epsilon` is a natural isomorphism whose `components` are
  exactly this real arrow, for every object of the existing constructible
  finite-Tor category. Thus neither arbitrary objectwise isomorphisms nor
  an arbitrary natural isomorphism serve as epsilon.
* At ring stages `RingRealization.star` realizes the result in the ambient
  derived category using the actual `PurCompactSupport.push`, i.e. ordinary
  derived direct image. `RingRealization.pull` and its `adjunction` equation
  fix the ordinary ringed pull/star adjunction. The conclusion is represented
  in the strictly full bounded constructible categories; their images lie in
  D+, so these ambient isomorphisms give the asserted D+ isomorphisms as well.
* `RingProjection` fixes the projection used by epsilon to the actual
  `PurCompactSupport.projectionMap`, including the proper-counit/open map and
  the two signed tensor symmetries. `ProjectionTensor.normalized` identifies
  its flat-representative comparison with the closed model's comparison;
  `nativeKFlat` explicitly relates the two K-flat presentations. The small
  site retains object universe u+1 and morphism universe u. `smallSite` is a
  real Mathlib size instance, not a hypothesis or an equality of universes.
* Naturality in M is the natural transformation inside
  `StageConclusion.epsilon`, on the opposite category. `StageConclusion.shift`
  says this transformation commutes with shifts. The imported triangulated
  opposite shift uses the negative shift on the original category: this is
  the `[-r]` convention, including negative integers.
* `DualShiftModel.signed` fixes the complex shift to `signedShift`, the
  actual signed Hom-complex comparison from `SignedDoubleHomCone.comparison`.
  Its product-component equation determines that witness; `signedShift` does
  not select unspecified data from a bare existence theorem. The coefficient
  Hom localization comparison and the chosen target representative's
  identification fix `DualShiftModel.realization.components`. Its
  `realizationShift` fixes the ambient shift by this model. The
  `RingShiftRealization` component equations identify the restricted shifts
  with `RingRealization.homX/homY`; the ordinary star comparison respects the
  existing derived pushforward shift. Thus the ring-stage shift structures
  in `StageConclusion` are normalized rather than freely chosen.
* `ScalarShifts` gives natural transformations with exactly the real
  evaluation-transposed Hom and pull/counit star components. Their CommShift
  laws carry the integral signed normalization through rationalization,
  rational scalar extension and common-stage passage, on the same stated
  dualizing pairs, without adding an arbitrary-input comparison isomorphism.
* `StageScalar` retains the operation comparisons `q` and its adjoint mate `b`,
  their unit/counit equations, the scalar unit, tensor comparisons, pullback
  comparison, and their projection square. Internal-Hom comparison is not an
  arbitrarily supplied isomorphism: `StageScalar.dualX/dualY` are obtained by
  transposing extended evaluation and kappa. `StageScalar.star` is the
  pullback/counit mate. `ScalarConclusion.exchange` writes the epsilon square
  using these arrows, including contravariance on the inverse q map.
* `Package.exchangeNaturality` gives the exchange equation for EVERY
  `StageScalar` comparison satisfying the dualizing square. Thus coefficient
  compatibility is independent of the choice of presentations for tensor
  and pull comparisons; the specified operation maps are included, rather
  than only a conveniently selected pair of comparison isomorphisms. Its
  hypothesis is exactly the already asserted c/kappa square, not an
  assumption of the theorem or a replacement for that square.
* `Package.ringScalar` handles every `Allowed` coefficient map: positive
  finite quotients, ramified extensions retaining exponent en, integral
  reductions, integral scalar maps, identities and composites. Its three
  explicit normalization equations are precisely the actual canonical
  compact-support `PurCompactSupport.comparison` equations. Its unit equation
  fixes the actual coefficient-unit map. The separate equations avoid falsely
  equating two presentations' CommShift structures.
* `Package.rationalization`, `.rationalScalar` and `.common` use the published
  rationalization, rational scalar-extension and common-inclusion functors.
  Their exceptional comparisons are required to equal the corresponding
  published System comparisons for f, a_Y and a_X. Each includes the two
  `ScalarConclusion` equations. Thus the field comparisons are through the
  integral and common finite-stage forms; no finite reduction of an arbitrary
  field-stage ambient object is invented.
* All coefficient Hom and star comparisons above are morphisms on these
  constructible domains. There is no assertion that coefficient change
  commutes with arbitrary ambient internal Hom, and no extra arbitrary-input
  Hom comparison isomorphism.

Dependency declarations read and used:

* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the recorded
  setting declarations `DerivedCategoryModule`, `constantComplex` and the
  bounded constructible finite-Tor predicates; `Sheaf.Paper.FiniteFieldFiber`
  supplies `FiniteFieldDatum`. The same datum is passed throughout.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.C`, `Stage`, `RingStage`, `Operation`,
  `System`, `Scalar`, `FieldComparison`, `Allowed`, `rationalization`,
  `rationalScalar`, `commonInclusion`, and the System's actual ring, field
  and common-stage comparisons. This node is already named in proof_deps;
  its structures organize the existing operations rather than introduce a
  new coefficient or functor notion. The original stmt_deps are retained.
* `Sheaf.Paper.DerivedPullbackTensorHom` and
  `Sheaf.Paper.SfDerivedDirectImage`: the existing derived-operation
  interfaces and their coefficient conventions.
* `Sheaf.CategoryTheory.RingedSiteDualityMaps`:
  `RingedSiteDualityModel`; `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, `CoefficientTensorModels.iso`.
* `Sheaf.Paper.ProEtaleCanonicalTensorPullback`: the actual original-site
  `proEtaleFlatRepresentatives`, `proEtaleOrdinaryTensor`, `ProEtaleTensorModel`.
  The published PurCompactSupport interfaces supply `pull`, `push`, `image`,
  `projectionMap`, `comparison`, and the left realizations.
* `Sheaf.Paper.FieldShriekCompositionQcqs`:
  `sfFieldShriekCompositionIntegral`; the integral compositor is used before
  rationalization, with the actual completed coefficient sheaf.
* `Sheaf.Paper.FiniteCoefficientAdjointComparisons` supplies the recorded
  ordinary finite-coefficient adjoint-comparison interface used by the
  coherent-system proof step. It is imported explicitly.
* Mathlib `CategoryTheory.Adjunction.Mates`: `conjugateIsoEquiv`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`:
  `SheafOfModules.unitToPushforwardObjUnit`.

`sk-def-sf-operations` has no lean record but its slopmaster2 audit is `closed`.
The 2026-10-18 standing-brief rule explicitly makes that audit usable without
restating the dependency. Read the full signatures/docstrings of its six audited
names: `AlgebraicGeometry.Etale.upperStar` (UpperLowerStar.Defs),
`rightDerivedLowerShriek` (Derived.LowerShriek), `rightDerivedUpperShriek`
(Derived.UpperShriek), `derivedTensor` (Derived.Tensor), `derivedHom`
(Derived.Hom), and `openImmersionLowerShriek` (LowerShriek.OpenImmersion.Defs).
The statement uses the published pro-etale/constructible realizations and
coefficient extensions of these operations. It does not identify the optional
ambient pro-etale adjoint with the unconditional constructible operation.

Edge cases checked: every finite exponent is ℕ+, so level zero is excluded;
quotients include m=n; ramified scalar changes retain en, not n; identities and
composites remain in Allowed; X or Y may be empty; f may be identity; no
connectedness, smoothness, properness, or ambient FullCD is assumed; both signs
of shifts are retained; integral data are completed before rationalization;
finite reduction at a field stage uses an integral representative. The theorem
is not disputed. No hollow data definitions or additional axioms were introduced.

Searches: `msearch.py leanfinder` with “Verdier duality exchanges compact support
pushforward with ordinary pushforward of the dual” returned eight sheaf
pushforward-composition hits, none the statement. Loogle for
`AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek`
returned no hit. Mathlib grep `verdierDual|VerdierExchange` in CategoryTheory
returned no hit. The three exact tool results are in searches.jsonl. Direct rg
searches in upstream WeilConjectures and shared lean/Sheaf found the upstream
finite étale Verdier theorem, the constructible System, tensor-Hom,
coefficient comparison and composition interfaces. The upstream theorem does
not state the all-stage original-site, canonical-map and coefficient-square
statement here; it is therefore not used as an existing match. The node marker
search found its source references but no matching all-stage theorem. No new
independent definition node and no dependency repair module is needed.

Validation: the initial dry run passed preflight and compilation. The final
version additionally pins the signed shift realizations and records comparison
presentation independence, and is recompiled and preflighted before delivery.
The final preflight metadata omits the local size instance from the public
declaration list; its implementation remains compiled.
Every delivered Lean file is compiled by the prescribed scompile.py
wrapper. The dry-run and delivery use deliver2.py; no direct Git mutation,
global build, or live-library write was performed by the worker.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
