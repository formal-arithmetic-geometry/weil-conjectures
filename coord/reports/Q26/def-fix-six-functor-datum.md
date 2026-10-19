## Worker report

Q26, 2026-10-19. This repair answers the immutable-head returns
`5ff2b0`, `b87e0dbee541`, `5595aa850620`, and `4dafee059b81`.
During the preceding repair attempt, the saved packet was inspected first and its initial dry run failed:
the unfinished finite-adjunction normalization fields did not elaborate. Those
types were repaired, and the previously unrequired integral normalization
record is now required by the main datum. The old report's claims that the
higher maps were already normalized were incorrect and are replaced here.

The delivery has three modules: `Sheaf.Paper.SixFunctorOperationDatum`,
`Sheaf.Paper.SixFunctorOperationDatumStages`, and
`Sheaf.Paper.CompactSupportReductionTowerConstruction`. The item owns the first;
the two new definition nodes below own the latter two. No definition contains
`sorry`; there are no new postponed theorems. The item's mathematical statement
is unchanged. Only its `lean` and its two added statement dependencies differ
from the shared item. All helper declarations are listed in their owner's
`lean.declarations`.

The five return points are addressed as follows.

1. **H3, finite domain.** `sixFunctorFiniteCategory` is now exactly
   `(intrinsicFiniteTorsionConstructible C.l E n hn X.obj.left).FullSubcategory`.
   Hence `finite.pull`, `finite.direct`, `finite.support`, `finite.exceptional`,
   `finite.openExtension`, `finiteDuality`, and `finiteVerdier` have the full
   bounded constructible domain. `sixFunctorFiniteHomPairs` tests the bounded
   output of the recorded ambient internal Hom on these full domains.
   `finiteTensorDomainStage` alone uses `finiteTorConstructibleCategory`.
   In `finiteExchangeProjection`, the two exchange transformations are
   precomposed with the full constructible inclusion, and the projection is
   precomposed in both variables with the finite-Tor inclusion. Their outputs
   are carried back by the canonical intrinsic derived realization.
2. **H3/H5, push comparisons.** The main structure now contains
   `finiteRefinementNormalization`, `finiteCompositionNormalization`,
   `finiteProperNormalization`, and `finiteOpenNormalization`. The first
   equates the realized component of `finite.comparison` with the recorded
   `refinementComparisonIsomorphism` at every retained origin witness and
   every identification with the actual input. It uses
   `sixFunctorFiniteWitnessSupport`, whose factors are the supplied operation
   realization, the input identification, and the section/K-injective-normalized
   `sfIntrinsicCompactSupportComparison`. The composition equation identifies
   `finite.composition.inv` with `coherenceProEtaleCompositor`, evaluated at
   the same witness and the three supplied compactifications. The proper
   equation uses the identity-open compactification and `sfIntrinsicOpenId`;
   the open equation uses the canonical identity direct-image comparison.
   `SixFunctorPushStage.exceptionalComparison` is now a definition using
   `Adjunction.ofNatIsoLeft` and `rightAdjointUniq`, rather than independent
   data. Its unit/counit compatibility is built into this adjunction comparison.
   The generic stage remains construction data; the main datum now requires
   `integralNormalization : SixFunctorIntegralNormalization D C E higher`
   and `coefficientIntegralNormalization` for every finite coefficient model
   used by `closure.coefficientStages`.

   The required record's `finiteLevels m` are the normalized finite operations
   at exponent `m+1`; `reduction m` is a `SixFunctorCoefficientComparison`
   using the actual `sixFunctorIntegralReduction`, rather than an arbitrary
   coefficient functor. Its `supportProjection` identifies the support
   reduction component with `sfCompactSupportChosenReduction`: the scalar
   adjoint of the chosen Roos projection. This is the same projection that
   `SixFunctorSupportConstruction` equates to the construction-owned tower
   projection. Its `directProjection` identifies the direct component with
   `sfDirectImageReductionComparison` of the retained direct-image Roos datum.
   Its `pullProjection` compares the actual pullback component, on every good
   K-flat representative and every identification with the input, with
   `integralPullbackFiniteComparison`. The auxiliary
   `sixFunctorIntegralReductionModel` uses the recorded derived scalar counit;
   `sixFunctorFinitePullbackModel` uses adjoint uniqueness preserving the
   canonical constant-section adjunction and its termwise derived factors.
   Its `openRealization` realizes the exact completed open extension, and
   `openProjection` equates the actual reduction component to
   `sixFunctorIntegralOpenReduction`, the canonical open scalar mate,
   with the unit-normalized finite ring presentation comparisons.

   The six returned maps occur in the following equations of that same
   `reduction m` record (they are required fields, not merely unused helpers):
   `compactification` for `integral.comparison`; `composition` for
   `integral.composition`; `properIdentity`; `openIdentification`;
   `directAdjunction.unit/counit` for `integral.pullDirectAdjunction`; and
   `openAdjunction.unit/counit` for `integral.openAdjunction`. The open
   adjunction's left and right isos are equated to its open-extension and
   pullback comparisons. `pullComposition` also preserves the finite
   normalized compositor. Thus all these equations use the four projection-
   or scalar-mate-normalized operation comparisons, not free endpoints.

   Rational maps satisfy these same six equations via `higher.rationalization`.
   `rationalModelNormalization` pins its support, direct, pullback and open
   comparison components to the identities on the integral object models. The existing pure-tensor formula
   in `SixFunctorSupportConstruction` fixes the rational functor's arrow map.
   Common-stage maps satisfy the same six equations via
   `closure.commonStageComparison E₀` for every finite model E₀, whose integral
   normalization is now required. `commonStageModelNormalization` pins these same four comparison components
   to the identity inclusions of the finite-stage values.
   Common-stage transition and inclusion cocycles remain required.
3. **H3/H5, exchange intermediates.** The finite accessor directly uses
   `derivedBaseChangeMap`,
   `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, and
   `projectionMapOfCompactification`. Thus no finite open-base-change,
   tensor-pullback, open-projection or support-identification field is supplied
   independently. The live projection source was read: it is the proper
   counit projection mate, followed by the inverse canonical open projection
   and `leftDerivedUpperStarCompactificationIso`. The live compact-support
   exchange source was also read: it is the proper derived base-change map
   followed by the canonical open-base-change isomorphism.
   For higher coefficients, `SixFunctorExchangeData` retains equations for
   each operation and adjunction. `openBaseChangeNormalization` fixes the
   inverse open exchange to `sixFunctorOpenBaseChangeInverse`, the transpose
   of the open unit under the pullback-composition square.
   `openProjectionNormalization` fixes every inverse component to
   `sixFunctorOpenProjectionInverse`, using that unit, inverse tensor pullback
   and the factorization `f = i ≫ p`. Both compact-support identifications are
   equated to `sixFunctorFactoredSupportIdentification`: composition, then
   open identification, then proper identification.
   `integralTensorPullbackNormalization`,
   `rationalTensorPullbackNormalization`, and
   `commonStageTensorPullbackNormalization`, together with their open-factor
   counterparts, fix the proper and open tensor comparisons to
   `canonicalIntegralPullbackTensor`, `canonicalRationalPullbackTensor`, and
   `canonicalCommonStagePullbackTensor` from the recorded comparison module.
4. **H5, transformation endpoints.** `SixFunctorTransformationComparison`
   is now a predicate taking its endpoints as arguments, with no free endpoint
   fields. `SixFunctorExchangeComparison.exchange` and `.compactExchange`
   pass `sixFunctorCompositeRealization` of the actual operation-realization
   isomorphisms from `SixFunctorCoefficientComparison`.
   `sixFunctorStageRealization` inserts only the recorded functor equalities.
   The projection comparison is the explicit component equation using the
   tensor, support and pullback realizations. It has no separately supplied
   source or target isomorphism.
5. **H8, unused refinement helper.**
   `sixFunctorFiniteRefinementComparison` is used on the right-hand side of
   `finiteRefinementNormalization`, which mentions the actual
   `finite.comparison` on its left-hand side. Its docstring now describes
   an imposed normalization that is present in the code. Every helper in
   the stage module, including this one, is recorded in `lean.declarations`.

Hypotheses and clauses of the item, read against the current blueprint update:

- `D : FiniteFieldDatum.{u}` is the global tuple `(p,a,q,k₀,k)`.
  `C : D.CoefficientDatum` supplies the prime different from `p` and the
  coefficient closure. `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`,
  and `[FiniteDimensional (Padic C.l) E]` supply the finite coefficient
  extension. The quotient ring, valuation ring and uniformizer are the
  published `Padic.coefficientExtensionRing`, `coefficientExtensionIntegers`
  and `coefficientExtensionUniformizer`. `n : ℕ` and `hn : 1 ≤ n` cover
  exactly the positive exponents; the case-split helpers include exponent one.
- `SixFunctorSpace D` is the full subcategory of `Over (Spec (.of D.k))`
  with locally finite-type and quasi-compact structure map. Morphisms retain
  their equation over this same base. A `Compactification f.hom.left` supplies
  the separated open/proper factorization; arbitrary nonseparated structure
  maps of the schemes are allowed. Open extension takes an explicit
  `IsOpenImmersion` argument. The normalization requiring separated finite-type
  `f` binds exactly those hypotheses. `hl : IsUnit (C.l : D.k)` records
  the coefficient invertibility already implied by the global setting.
- Clause (1): `finitePullback` and `finiteDirectImage` realize the full-domain
  stage as `finiteDerivedPullback` and `proEtaleConstantDerivedDirectImage`.
  `finiteTensorNormalization` and its map equation fix the finite-Tor tensor
  to `finiteIntrinsicDerivedTensor`, on objects and morphisms.
  `sixFunctorFiniteHom` is the literal restriction of
  `finiteIntrinsicDerivedInternalHom` to its bounded-output pairs.
  Higher pullbacks, tensors and Hom use `constructibleIntegralPullback`,
  `constructibleIntegralTensor`, `constructibleIntegralHom`, their raw
  rationalizations, and the recorded common-stage constructions.
  `integralDirectImage` and `integralDirectLimitObject` retain the completed
  direct image and its Roos vertex; rational/common-stage images retain their
  coefficient comparisons and pullback adjunctions.
- Clause (2): open extension and compact support are realized as the recorded
  exact extension by zero and `sfIntrinsicCompactSupport` in the finite case.
  The normalizations in point 2 above retain the prescribed comparison,
  composition and proper identification. `SixFunctorSupportConstruction`
  retains the integral tower, total derived inverse limit, scalar actions,
  object value and projection equation, and the rational pure-tensor morphism
  formula. `commonStageSupportValue` is the specified finite-stage inclusion
  of `sfQbarCompactSupportValue`. The common-stage functors act on the actual
  common-stage category, including morphisms.
- Clause (3): the finite accessor contains the three canonical natural
  transformations in intrinsic output coordinates. Its compact-support
  target uses the canonical pulled-back compactification. Higher maps are
  exactly `.stage.exchange`, `.stage.compactExchange`, and `.stage.projection`
  from `ExchangeProjectionStage`, with the normalizations in point 3.
  Rationalization, finite scalar transitions and common-stage inclusions
  retain the comparison squares in point 4.
- Clause (4): each push stage supplies `support f c ⊣ exceptional f c` on
  its bounded constructible categories. `finiteExceptional` realizes the
  finite functor as the existing etale-transported `sfFiniteExceptional`.
  Refinement of right adjoints is constructed from the normalized support
  comparison. No ambient exceptional-adjoint-admissibility hypothesis occurs.
  The separate preservation and existence theorems are not asserted here.
- Clause (5): `SixFunctorDualityData.dualizing` is the exceptional image of
  that same stage's coefficient unit under the structure map.
  `.verdier` applies the recorded internal Hom to this very object.
  `dualPair` supplies its bounded-output condition for every constructible
  input. `finiteVerdier`, `integralVerdier`, `rationalVerdier` and
  `commonStageVerdier` retain all four coefficient levels. Separatedness of
  the structure map occurs exactly in these dualizing constructions.
  Neither purity nor biduality is part of this definition.

Dependency declarations read and used (module paths all start with `Sheaf.`
unless explicitly specified):

- `Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.CoefficientDatum`.
- `Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`.
  `Paper.FiniteTorAmplitude`: `finiteTorConstructible`, its category,
  `finiteTorConstructibleIntegral`, and `finiteTorFieldCoefficientCategory`;
  `Paper.FiniteTorAmplitudeSites` retains the recorded etale presentation.
- `Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its category;
  `Paper.SfRationalizationKaroubi`: the raw
  `sfRationalConstructibleCategory` and localization;
  `Paper.GeneralAlgebraicallyClosedCoefficients`: the actual stage system,
  inclusions and `generalAlgebraicallyClosedConstructibleCategory`.
- `Paper.DerivedPullbackTensorHom`: the finite, integral, rational and
  common-stage pullback/tensor/Hom constructions;
  `Paper.CompletedPullbackTensorComparison`: the three named canonical
  higher-coefficient pullback-tensor comparisons.
- `AlgebraicGeometry.SfIntrinsicCompactSupport`: `sfIntrinsicCompactSupport`;
  `AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`;
  `AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedEquivalence` and the normalized direct-image comparison.
- `Paper.RefinementComparisonIsomorphism`:
  `RefinementFiniteLevelOrigin`, `refinementFiniteLevelFixedObject` and
  `refinementComparisonIsomorphism`;
  `Paper.CompactificationCoherence`: `compactification_coherence`, whose
  refinement normalization is what the main datum records;
  `Paper.CompactSupportSiteCoherence`: `coherenceProEtaleCompositor`.
- `Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage`, its
  three maps, `ExchangeProjectionComparisonPreserves`, and
  `ExchangeProjectionAdjunctionComparison`.
  The two current finite canonical modules were read using `scompile.py
  --source WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.
  LowerShriekBaseChange` and `.LowerShriekProjection` (without the displayed
  line break). No legacy duplicate finite-operation module is imported.
- `AlgebraicGeometry.SfFiniteExceptionalInverseImage`: `sfFiniteExceptional`.
  The current exceptional dependency's
  `Paper.ConstructibleExceptionalAdjunctionCoefficients.System` and
  `Paper.ExceptionalAdjointAdmissibility` were read to check the distinction
  between construction/adjunction data and an ambient admissibility assumption.
- `Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage` and
  `SfIntegralDirectImage`; the current direct-image record also reexports
  these through `Paper.SfCommonStageDirectImage`.
  `Paper.IntegralRationalQbarCompactSupport`: the three support values;
  `Paper.QcqsCompactSupportRealization`: its projection-normalized realization
  of those same values. The delivery retains the construction-owned tower
  normalization instead of selecting arbitrary data from existence.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and its topology;
  the morphism-properties dependency is a convention node with no declaration.

Edge cases checked: the empty scheme, identity morphisms, proper maps with
identity open factor, open immersions with identity proper factor, identity
refinements and successive refinements, identity/successive coefficient
extensions, exponent one, and all larger positive exponents. At a nonregular
finite quotient the residue-field object may fail finite Tor amplitude: it is
still admitted by pullback/direct image/support/exceptional/duality and by both
exchange inputs, and is excluded only from the finite-Tor tensor/projection
domains. Exponent zero is excluded by the source's `n ≥ 1`. No extra equality
between the site's object and morphism universes was introduced.

Searches: the node and both new nodes retain their original LeanSearch,
LeanFinder/Loogle, Mathlib grep and project/DAG searches. In this repair,
`msearch.py ... leanfinder "six functor operation datum with normalized
compactification comparisons exchange projection and Verdier duality"` returned
8 generic triangulated-functor/adjunction/square results, no assembled datum.
`msearch.py ... loogle "CategoryTheory.Functor, CategoryTheory.Adjunction,
DerivedCategory"` returned 0 results. `rg` for `SixFunctorOperationDatum`,
`sixFunctorFiniteRefinementComparison` and
`SixFunctorTransformationComparison` found no declaration in the read-only
upstream project or shared `lean/Sheaf`; the Mathlib algebraic-geometry search
for `SixFunctorOperationDatum|six.functor.*datum` also found none. The exact
canonical comparison declarations were located in their published modules
and reused. The earlier LeanSearch service failure is recorded as unavailable,
not as evidence of absence.

Validation history: the preceding attempt's initial saved-packet dry run failed with concrete elaboration
errors. The finite pullback helper now directly uses the canonical intrinsic
pullback at positive n; its quotient is finite by the named positive-quotient
theorem. This removes the opaque case split from the normalization endpoints.
All compiles use the prescribed server `scompile.py`; final results are recorded
below after the current repair compiles and passes preflight.

## New nodes

`def-sf-operation-stages` owns the generic construction-stage records,
compactified squares, normalized exchange/realization helpers, coefficient
comparison squares, higher stages, and duality construction. It serves the
five clauses of the existing blueprint item; its statement introduces its own
base/category data and cites all its constituent notions. The new-node search
records contain the required semantic, name and repository searches. No exact
assembled construction-stage declaration was found. Its helper signatures,
source/blueprint docstrings and complete declaration list were reread.

`def-weil-compact-support-reduction-tower-datum` owns the coherent strict tower,
all evaluation/transition equations, normalized scalar actions, exactness/shift
data, and the total right-derived-limit unit and projection normalization.
Its source is main-20261015, sec-six-functors-basics/sk-prop-int-brown,
`def-weil-integral-rational-qbar-compact-support`, displayed derived-limit
formula. Its earlier searches found no exact bundled datum. The Lean index
`m : ℕ` denotes positive exponent `m+1`. Its statement and implementation
use the derived-functor unit on complexes, not a unit to a constant tower.
The tower source is unchanged from the returned packet and was recompiled.

## Dependency modules

None. The two additional modules have the new-node owners listed above.
No published dependency file or dependency-node binding was changed.

## Second reading by Q26

I read the current main-20261015 source of the item (order 1850) and the
integral/rational/common-stage support definition (order 1849), the live return
entry, all three saved modules and node records, and the canonical dependency
interfaces used in the repair. The detailed hypothesis and clause mapping is
above. The source asks for the constructed maps, not just object values; that
was the outstanding defect in the returned packet. The repair changes both
the stage module and the main datum that requires its new normalizations.

For refinement, composition, proper and open identification I traced the
actual integral maps through `reduction m` to the finite maps, using the
normalized support/direct/pull/open comparisons listed above. For both
adjunctions I checked that the comparison record retains unit and counit
equations and uses the same left and right operation realizations. Finite
adjunction normalizations compare to the recorded ordinary-unit-normalized
intrinsic adjunctions. Rational and common-stage maps are constrained through
the same six coefficient-change equations; their four operation-realization components
are additionally fixed on the actual object models by
`SixFunctorCoefficientModelNormalization`.

The zero object and empty scheme are admitted. Positive index m+1 includes
exponent one. Identity refinements, proper maps with identity open factor,
open immersions with identity proper factor, and successive refinements use
the same normalization equations. The K-flat representative condition in
pullProjection tests every good representative and every identification e;
it adds no hypothesis on the original input. The original finite category
continues to contain every bounded constructible object, with finite-Tor
restrictions only for tensor/projection. No site universe equality, ambient
exceptional-admissibility assumption or data-body sorry was added.

The item's mathematical statement and source remain unchanged. The two new
nodes retain their source ownership; their declaration registries include all
new helpers. The tower module's construction is retained. No shared source,
launcher tool, direct Git command, global build or other agent was used.

Fresh repair searches, 2026-10-19: `msearch.py ... loogle
"CategoryTheory.Adjunction.leftAdjointUniq"` returned the existing Mathlib
adjoint-uniqueness isomorphism and its 11 normalization/coherence lemmas;
this is the primitive used in the finite pullback model. `msearch.py ... grep
"SixFunctorIntegralNormalization|SixFunctorCoefficientModelNormalization"
CategoryTheory` returned zero hits. `rg` for the new normalization names in
both live `lean/Sheaf` and `lean/WeilConjectures` returned no declaration.
These are helpers of the existing construction-stage notion, not replacements
for the project's reduction or compact-support definitions.

The repaired files type-checked in `scompile.py` (tower 9.7 s, stage 57.6 s,
main 5.9 s). That run reported one line-length warning at the finite pullback
model; the line has been wrapped, and final clean validation follows below. Elaboration profiling identified expensive
unfolding in generated structure declarations; the canonical model helpers
use the dependency-required transparency, while the normalization record
uses explicit representative-localization types and normal transparency.
No file was split and no compile limit was raised for this repair.
The fresh semantic search for “six functor datum normalized coefficient
reduction compact support composition and adjunction maps” returned eight
generic sheaf/adjunction results, with no assembled normalization datum.

Resumption validation, 2026-10-19: inspected the retained report and ran
`deliver2.py Q26 def-fix-six-functor-datum --no-push` before changing the packet.
It passed preflight and all three file compiles (dry-run commit `ed2b8352af`).
The substantive normalization repair was already preserved in the sandbox;
both main and stages differ from the saved pre-repair copies. This resumption
retains that repair, rather than restoring any of the four returned versions.
The required main fields are `integralNormalization` and
`coefficientIntegralNormalization`; the required higher-stage fields are
`rationalModelNormalization` and `commonStageModelNormalization`.
The six coefficient-comparison equations were reread against these required
fields and the actual projection/scalar-mate endpoints.

A fresh explicit `scompile.py` invocation compiled all three delivered files
in dependency order with no errors or warnings: tower 9.7 s, stages 50.5 s,
main 6.0 s. Node signature strings occur verbatim in their owning files;
all delivered Lean lines have length at most 100, all variables and universes
are explicitly bound, and no delivered file contains a `sorry` token.
The item differs from the current shared node only in `lean` and the two
new-node additions to `stmt_deps`. Its mathematical statement is unchanged.
The delivery wrapper refreshes the base and performs the authorized rebase;
no direct Git command or shared-file edit was used.
