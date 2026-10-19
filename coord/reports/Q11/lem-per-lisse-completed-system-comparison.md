## Worker report

Item: lem-per-lisse-completed-system-comparison. Group Q11, stage 2, 2026-10-18.
Module: `Sheaf.Paper.LisseCompletedSystemComparison`.
Declaration: `AlgebraicGeometry.ProEtale.CompletedLisse.completed_system_comparison`.
The item helpers remain in its namespace and its `lean.declarations`; dependency definitions
are recorded by definition nodes using their existing published declarations.

The theorem asserts `Nonempty (System.{u} l)`. The structure expands the full comparison,
including its functors, canonical-map normalizations, and identity/composition equations.
It does not assume any comparison maps, equivalences, or lattice existence as hypotheses.
Every helper definition has actual data. The one postponed theorem is this item's named
statement, with source and the complete ten-step natural-language proof in its docstring.
No theorem asserting essential surjectivity of rational realization is included.

### Hypotheses and coefficients

* Prime ell: `(l : ℕ) [Fact l.Prime]`, explicitly bound at the theorem and helper declarations.
* Finite E/Q_l: `Base.E`, `Base.field`, `Base.algebra`, and `Base.finiteDimensional`.
  The topology in all coefficient declarations is the recorded spectral-norm topology.
* A and the chosen uniformizer: `Integers l P` is precisely
  `Padic.coefficientExtensionIntegers l P.E`; every quotient and multiplication map uses
  `Padic.coefficientExtensionUniformizer l P.E`, not an extra chosen parameter.
* X Noetherian, separated, ell invertible: `Base.X`, `Base.noetherian`, `Base.separated`,
  `Base.invertible : ∀ x : X, Invertible (l : X.residueField x)`.
* Pro-etale site: `Scheme.ProEt` and `ProEt.topology` on the actual scheme, with site
  object universe u+1 and morphism universe u. Coefficients/modules use universe u+1;
  no equality between the site object and morphism universes is imposed.
* B_X: `completedRing l P` is `adicLisseCompletedRing` for the principal uniformizer ideal,
  the actual inverse limit of the constant finite quotient commutative-ring sheaves.
  Index n denotes positive exponent n+1 throughout. There is no quotient at exponent zero.
  The adic coefficient datum uses function-sheafified finite levels; the proof explicitly
  invokes completed-constant-sheaf-reduction to identify those with these constant levels.
* Identification with continuous integral coefficients: `Comparison.coefficientIso`, fixed
  on every residue projection by `coefficient_projection`. The existing
  `IntegralLisseReductionEquivalence` supplies the continuous coefficient cone and its limit.
* E_X=B_X[1/varpi]: `rationalRing l P` is the recorded `lisseFieldSheafSized`, and the
  coefficient map is `coefficientIso.inv ≫ lisseIntegerToFieldSized`. The recorded
  `integralComparison` includes the localization cocone and its fraction formula for
  continuous A -> continuous E, at ell. This is the same localization at varpi because
  ell is a unit times a positive power of varpi in the DVR. This identification preserves
  the coefficient inclusion, not just the abstract isomorphism class of the ring.

### Each clause of the conclusion

* Lisse integral and rational modules are `Integral` and `Rational`: the existing
  `SheafOfModules.isFiniteLocallyFree` full subcategories over the actual coefficient ring
  sheaves. This notion permits locally varying finite ranks and rank zero.
* Normalized inverse systems are `Systems`: a full subcategory of the recorded
  `LisseIntegralSheaf` category. That category already imposes finite local constancy,
  annihilation by varpi^(n+1), and stalkwise surjective transition with kernel the required
  ideal multiple. These are precisely the stated normalized quotient transition maps.
  `IsFreeSystem` imposes, at each level and each geometric stalk, an integral-linear
  isomorphism with `(A/varpi^(n+1))^r`. For a finite locally constant module sheaf this
  is exactly finite local freeness over the quotient. The residue transitions force local
  rank agreement, so no global rank or extra connectedness hypothesis is imposed.
  This restriction matters: the existing Weil II category also allows finite torsion
  modules and cannot itself be substituted for the finite-free category in this node.
* The integral equivalence is `Comparison.equivalence : Integral l P ≌ Systems l P`.
  `reduction` is a compatible family of actual maps from the underlying module sheaf to
  the etale-to-pro-etale pullback of its tower. `reduction_quotient` says every map is
  the cokernel of multiplication by varpi^(n+1). `reduction_scalar` fixes its A-linear
  action; `reduction_natural` fixes the morphism map. Thus this is the actual reduction
  functor, not an unspecified equivalence of categories.
* The inverse is the actual inverse limit of nu_X^* N_n: `proEtaleDiagram` uses the
  canonical `supportSiteComparisonCoefficientPullback` at every level; `completion` is
  its cone with vertex the underlying sheaf of the inverse functor's object;
  `completion_limit` is its `IsLimit` universal property. Sheaf-module limits are computed
  on underlying abelian sheaves, with the action prescribed by the coefficient projections.
  `completion_natural`, `unit_projection`, and `counit_projection` identify its morphism
  map and equivalence unit/counit on the actual residue projections. The scalar equations
  also retain the coefficient actions when using underlying abelian sheaves in these cones.
* Raw A-linear localization: `RawRational` is the finite-free full subcategory of
  `LisseRationalSheaf`, whose objects are integral systems and whose Hom is the recorded
  `E ⊗[A] Hom`. This is equivalent through the displayed integral equivalence to the raw
  localization of lisse B-modules. It is not an idempotent completion or a category of
  rational sheaves with an assumed global lattice. `rationalObject` identifies the realized
  object with the actual `completedAdicChange` scalar extension to E_X.
  `rational_map` sends a pure tensor a tensor f to a times the scalar extension of f;
  `rational_add` determines the induced additive map on all tensors.
  `rationalFullyFaithful` is exactly full faithfulness, with no essential-surjectivity field.
* Module pullback and finite coefficient extension: `Arrow` simultaneously records a scheme
  map Q.X -> P.X and a Q_l-algebra map P.E -> Q.E. Between finite extensions it is a finite
  coefficient inclusion. Identity coefficient map gives pure scheme pullback; identity
  scheme map gives pure coefficient extension. Mixed cases are included as well.
* Actual coefficient maps: `RingOperation.integral_sections` and `rational_sections` fix
  the maps on EVERY continuous function, at EVERY point of each pulled-back pro-etale
  object, by composition with `pullback.fst` and the coefficient inclusion. The completed
  map is fixed by `completed_normalization`, and `localization_square` fixes the square
  with E_X. No arbitrary ring map or map specified only on constants is substituted.
* Actual module operations: `RingOperation.integralPush` and `rationalPush` are the
  existing sectionwise module direct images with these ring maps. `ModuleOperation`
  specifies the full ambient module adjunctions to these fixed right adjoints, and their
  restrictions to lisse modules. Thus their left adjoints are the genuine ringed tensor
  pullbacks. Their universal units, `integralUnit` and `rationalUnit`, are the normalized
  maps x -> 1 tensor x. Specifying these universal properties constructs exactly the
  needed pullbacks without collapsing site universes or adding a flatness hypothesis.
* Finite-level operations: `sourceIndex` is the recorded ceil((m+1)/e)-1. `finiteLevel`
  uses the actual etale inverse image, then `Sheaf.ringExtendScalars` along the recorded
  `lisseScalarCoefficientMap`, and finally restriction along the target quotient map.
  `finiteScalarUnit` is the scalar-extension adjunction unit followed by sheafification;
  `finiteEtaleUnit` composes the actual pullback and scalar-extension units.
  `EtaleOperation.level` identifies every output level with this exact tensor operation,
  naturally in the input system. `Operation.etale_transition` fixes the transition maps
  by these units, including coincident consecutive source indices under ramification.
* Canonical etale/pro-etale transport: `EtaleOperation.proEtaleUnit` is the adjoint mate
  formed from the canonical `supportSiteComparisonCoefficientPullbackIso` and the
  finite-level etale unit. It supplies the precise comparison between the two sites.
* Reduction commutes with the operations: `Operation.reduction` is the natural iso.
  `reduction_normalization` identifies its every residue map with the finite unit just
  described, after the actual module-pullback unit. It is the map on quotient tensors.
* Inverse-limit reconstruction commutes: `Operation.reconstruction` is the natural iso.
  `reconstruction_normalization` identifies its every limit projection with that same
  finite unit and the source projection at the ramified source index. This is a statement
  on lisse objects, not a claim that arbitrary inverse image preserves arbitrary limits.
* Rational realization commutes: `Operation.raw` is the operation on the raw localized
  category; `rawIntegral` ties its objects to finite scalar extension, and `raw_map` plus
  `raw_add` prescribe the coefficient-semilinear map on every pure tensor and sum.
  `Operation.rational` is the realization comparison. `rational_normalization` fixes it
  on sections 1 tensor x using the actual `completedAdicChangeTensor` generators and
  the integral reconstruction comparison. E-linearity then fixes every fraction.
* Identity and composition equations: `System` quantifies over every allowed `Base` and
  every `Arrow`, including both identity operations and arbitrary composites. Its
  integral/rational identity and composite isomorphisms are fixed by their equations on
  the actual adjunction units and `lowerStarId`/`lowerStarComp`. These are respectively
  1 tensor x -> x and c tensor (b tensor x) -> cb tensor x.
  `reduction_id`, `reconstruction_id`, `realization_id` are the three identity squares.
  `reduction_comp`, `reconstruction_comp`, `realization_comp` are the three composite
  squares, as equalities of natural transformations. The etale and raw identity/composite
  isos are thereby tied to those same canonical module maps through the equivalence and
  fully faithful realization. Composites of two scheme maps, two field inclusions, and
  mixed pairs are all covered; none is silently omitted.

### Dependency declarations used

Original statement dependencies were read with their complete recorded signatures/docstrings:

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public base coefficient
  module: `Padic.finite_coefficientExtensionRing`, `coefficientExtensionIntegers`,
  `coefficientExtensionUniformizer`, `coefficientExtensionIdeal`, `coefficientExtensionRing`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
* `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficients.coefficientRing`, `ringSystem`,
  `completedRing`, `completedReductionTower`, and `completedAdicChange` with
  `completedAdicChangeTensor`. Its public `Sheaf.Paper.AdicLisseModule` supplies
  `adicLisseRingSystem`, `adicLisseCompletedRing`, `adicLisseForget`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the actual
  `SheafOfModules` category; Mathlib's existing `SheafOfModules.isFiniteLocallyFree`.
* `Sheaf.Paper.LisseIntegralSmallCoefficients`: `Scheme.LisseIntegralSheafOfUniverses`;
  its public `Sheaf.Paper.LisseAdicSheaves` supplies the equivalent size-appropriate
  `AdicIntegralDiagram`, `IsLisseIntegralDiagram`, `LisseIntegralSheaf`,
  `LisseRationalSheaf`, `lisseIntegerInclusion`, `lisseScalarSourceIndex`,
  `lisseScalarSourceIndex_le`, and `lisseScalarCoefficientMap` used here.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and
  `proEtaleSiteComparisonModules`.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleSheafInverseImage`,
  `proEtaleBaseChange`, `proEtaleSheafDirectImage`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, with its public site tensor API.

The expanded statement uses these definition-node interfaces. The two new nodes
record existing declarations and deliver no definition modules:

* `def-per-integral-lisse-reduction-data`:
  `Sheaf.SixFunctors.IntegralLisseReductionEquivalence`,
  `ProEtale.IntegralLisseReductionEquivalence`, `integralLisseScalar`,
  `integralLisseReduction`, `integralLisseRing`. The coefficient witness is retained
  explicitly, rather than an unverified identification of continuous and completed rings.
* `def-weil-pbc-lisse-lattice-coefficients`:
  `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`,
  `ProEtale.lisseIntegerSheafSized`, `lisseFieldSheafSized`,
  `lisseIntegerToFieldSized`, `lisseFieldConstantSized`.
* `def-weil-pbc-adic-lisse-module`:
  `Sheaf.Paper.AdicLisseModule`, `Scheme.IsAdicLisseModule` and the completed ring helpers
  listed above. Existing `isFiniteLocallyFree` is used directly for the finite-free subcategory.
* `def-per-site-comparison-pullback-data`:
  `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`,
  `supportSiteEtaleComparisonPullback` and its adjunction,
  `supportSiteProEtaleComparisonPullback` and its adjunction,
  `supportSiteComparisonCoefficientPullback` and `supportSiteComparisonCoefficientPullbackIso`.

The original proof-dependency modules are imported, with their full source signatures read:
`Sheaf.Paper.CompletedConstantSheafReduction` (including the finite-constant final clause),
`Sheaf.AlgebraicGeometry.ProEtaleFiniteLocalSystemsTwist`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`,
`WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, and
`Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`.
The finite tensor unit additionally uses the existing
`Sheaf.Algebra.Category.ModuleCat.RingScalarExtension` API:
`Sheaf.ringExtendScalars`, `ModuleCat.ringExtendScalarsAdj`, and `toSheafification`.
The two existing modules are publicly imported because their definitions occur in
the statement, and their theorems also belong to the unchanged proof plan. Their
sources and node records are reused unchanged.

### Sources and edge cases

Read the local Bhatt--Scholze paper at Corollary 5.1.5, Lemma 6.8.2, Definition 6.8.3,
and Proposition 6.8.4(1),(4), together with the node's ten proof steps. The source only
claims full faithfulness globally in the rational case; local lattice existence is a
separate assertion, so it is not silently strengthened to a global equivalence here.

Checked before/during formulation:

* Empty scheme: all module sheaves vanish; geometric-stalk freeness is vacuous, all
  normalized towers and all maps are unique. No nonemptiness or positive rank is added.
* Rank zero, disconnected schemes, and varying finite local ranks: finite-local-freeness
  and the stalkwise existential rank admit these; no uniform rank is quantified.
* First level: the index 0 means A/varpi, never A/(1). Transition from index n+1 to n
  has the recorded kernel varpi^(n+1); coefficient maps use positive exponents.
* Finite torsion counterexample to using the unrestricted existing system category:
  constant torsion towers satisfy its finite-module condition but are not generally
  free over every A_n; `IsFreeSystem` explicitly excludes them where appropriate.
* Ramification e=2: target exponent m uses source exponent ceil(m/2), so consecutive
  target levels can have the same source index. Transitions include the identity source
  map in that case. The finite target quotient is not assumed free/flat over the
  smaller source quotient; the real scalar extension is used.
* Identity field inclusion, identity scheme map, two field inclusions, two scheme maps,
  and mixed composites all occur among `Arrow`, `identity`, and `composite` and are
  quantified in `System`'s equations. Different chosen uniformizers remain harmless:
  the actual recorded coefficient quotient map and source index are used at every level.
* Noetherian X is qcqs; the global denominator bound needed for rational Hom full
  faithfulness is obtained by the cited bounded-continuity theorem, not asserted for
  arbitrary non-quasicompact schemes.
* Ambient module pullbacks are fixed by genuine adjunctions to the actual direct image.
  They are not arbitrary functors, and their comparisons are fixed by residue/tensor
  normalizations, avoiding a mere unspecified natural-isomorphism existence statement.

### Searches

Searches were made before choosing the category and comparison interfaces:

* `msearch.py ... leanfinder` query:
  `lisse completed integral sheaves equivalence normalized finite etale module systems rational realization fully faithful`.
  Eight hits; etale forgetful full faithfulness and condensed locally-constant-module full
  faithfulness were unrelated. No complete comparison statement was found.
* `msearch.py ... loogle` query:
  `CategoryTheory.Localization, CategoryTheory.Linear, SheafOfModules.IsFiniteLocallyFree`.
  Zero hits (the expected `CategoryTheory.Localization` name was not known).
* `msearch.py ... grep` query `Lisse|lisse|Normalized.*System` in `AlgebraicGeometry/Sites`.
  Zero hits for this comparison.
* `msearch.py ... leansearch` query:
  `completed lisse module sheaves equivalent normalized finite etale systems localization fully faithful`.
  Eight hits, including condensed locally-constant full faithfulness and
  `SheafOfModules.fullyFaithfulForget`; none states completed reduction, normalized finite
  etale towers, rational realization, and the specified coherent comparisons.
* `rg` of the item id in upstream `WeilConjectures`: no existing declaration.
  Searches for lisse equivalences in `lean/Sheaf` found the existing integral
  reconstruction module, which is used, but not this finite etale/rational/coherent result.
* Targeted `rg` searches in Mathlib and both project source trees located/reused
  `isFiniteLocallyFree`, the normalized Weil II system categories, coefficient scalar
  extension, site comparison mates, sheafified tensor scalar extension and module
  pushforward adjunction interfaces. Their signatures and docstrings were read.
* `tools/blueprint_refs.py ancestor lem-per-lisse-completed-system-comparison` returned
  `lem-per-smooth-pullback-t-exact`, consistently with this item's blueprint provenance.

There is no STATEMENT-DISPUTED claim or statement correction. The item's mathematical
statement, proof and proof dependencies are unchanged. Two added statement prerequisites
are the new definition nodes recording existing declarations; the two other already-landed
definition prerequisites are retained.

### Validation and returned collision repair

Return L at immutable head `8a66bca050e3` identified 15 duplicate declarations in
`IntegralLisseReductionData`. The saved packet was dry-run first as requested: commit
`9624eefd3e` passed preflight and compiled after server confirmation of an initial local
timeout. Its self-check still found the returned ownership collision. The live source was read with `scompile.py --source` for both original modules. Removing docstrings
and whitespace, all 15 integral declarations and all 16 site-comparison declarations in
the extracted modules exactly match the published originals. Thus reuse is exact.

The two definition nodes now have `existing: true`, branch `newtargets-dag`, and module
paths `Sheaf.SixFunctors.IntegralLisseReductionEquivalence` and
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`. Their declarations retain
their original names. Both copied definition modules and both replacement theorem modules
were removed from this delivery, along with the two dependency-node edits. The item imports
the existing modules publicly. The entire item module from its module docstring onward,
including every definition body, theorem signature and ten-step proof docstring, is unchanged.
This repairs all 15 listed collisions and the analogous site-comparison duplication.

The theorem still has exactly one postponed proof, `completed_system_comparison`.
`autoImplicit` is false; universe `u` is explicit. There is no statement correction.
The compile and delivery wrappers validate the remaining delivered file and probe every
existing declaration named in the two definition-node records.

## New nodes

`def-per-integral-lisse-reduction-data` records the existing
`AlgebraicGeometry.ProEtale.IntegralLisseReductionEquivalence` and its 14 helpers in
`Sheaf.SixFunctors.IntegralLisseReductionEquivalence`; it introduces no Lean definition.
Its statement describes the actual continuous coefficient sheaves, scalar cokernel quotients,
finite-free module and normalized tower categories, coefficient limit/localization data,
and projection-normalized reduction equivalence TYPE, without asserting inhabitance.
The source is BS 6.8.2, 6.8.3 and 6.8.4(1). Each stated parameter and property matches
the corresponding existing binder or structure field. `finiteConstant_sections` fixes
constant sections; `coefficientCone_app`, `coefficientLimit`, `coefficientQuotient` fix
reductions; `localization_app`, `localizationColimit` fix fractions; `reductionQuotient`,
`completionLimit`, the naturality fields and unit/counit projection fields fix the equivalence.
The recorded LeanSearch and LeanFinder hits are unrelated, Mathlib/upstream grep found no
match, and project/DAG searches found the existing helpers in the theorem module but no
definition node recording their type. The node therefore binds those existing definitions.

`def-per-site-comparison-pullback-data` records the existing
`AlgebraicGeometry.ProEtale.supportSiteComparisonPullbackCoherent` and its 15 helpers in
`Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`; it introduces no Lean definition.
Its Stacks 098T, 099R, 00WX and 0B65 statement describes the actual Kan-extension/sheafification
inverse images, canonical adjunctions, restriction comparisons and their adjunction mates,
then defines the identity/composition/Cartesian-square coherence PREDICATE without asserting it.
The existing generic coefficient binders supply the stated colimits and weak sheafifications.
The three conjuncts of `supportSiteComparisonPullbackCoherent` are precisely those equations.
`supportSiteComparisonCoefficientPullback D X` unfolds to the same constructed pullback as
`comparisonUpperStar D X` for its applicable abelian coefficients and to the inverse image
of `proEtaleSiteComparison X` for sets. The recorded searches found generic Mathlib results
and the existing project helpers, with no definition node recording this predicate.

### Self-check by Q11

Read the item node and all 649 lines of its module. `Base` binds the prime, finite extension,
Noetherian separated scheme and invertibility; `Integral`, `Systems`, and `RawRational`
give the exact categories. `Comparison` records reduction, cokernel and limit maps, their
unit/counit projections and rational full faithfulness. `Operation` retains the ramified
finite-level tensor units and every comparison normalization; `System` retains identity,
arbitrary composition and mixed operations. Empty schemes, zero/varying rank, positive-level
indexing, ramified repeated source indices, and identity coefficient extensions remain covered.
The ownership mismatch in the return is repaired by import and reuse. No mathematical
hypothesis, clause, universe, map normalization, declaration name or definition body changed.
This is a worker self-check; the maintainer performs the independent review.

Repaired-file validation: the prescribed `scompile.py Q11
lem-per-lisse-completed-system-comparison lean/Sheaf/Paper/LisseCompletedSystemComparison.lean`
completed with exit 0 in both sandbox and library checks, with no errors or non-sorry
warnings. No copied dependency module participated in this check.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
