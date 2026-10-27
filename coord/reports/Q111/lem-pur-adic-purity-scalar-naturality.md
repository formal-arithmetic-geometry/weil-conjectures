## Worker report

Item: lem-pur-adic-purity-scalar-naturality. Group Q111, stage 2.
Module: `Sheaf.Paper.AdicPurityScalarNaturality`.
Main declaration: `WeilConjectures.AdicPurityScalarNaturality.adicPurityScalarNaturality`.

This is a simultaneous existence statement, with a single postponed theorem.
The helper definitions construct the stated source and scalar functors and their
canonical maps. `Data` packages the conclusions; none is a hypothesis of the
main theorem. No arbitrary-lift uniqueness is asserted. The stage-1 repair note
is resolved: Q124 re-split the proof, and the current node has no prior Lean
binding to preserve. No mathematical statement correction is needed.

### Hypotheses and objects

- `D : FiniteFieldDatum` supplies p prime, a positive, q=p^a, the finite base
  field, its cardinality, and the fixed algebraic closure k.
- `C : D.CoefficientDatum` supplies the distinct coefficient prime and fixed
  algebraic closure of Q_l. `Field D C` is the existing
  `Padic.FiniteCoefficientFields C.l C.Qbar`; it includes every finite subfield,
  including the base field. `E.val` is its existing intermediate-field carrier.
  No extra norm, topology, uniformizer, or algebraic closure is chosen here.
- The `Over (Spec (.of D.k))` instances on X,Y and `f.IsOver` express the
  specified k-schemes and k-morphism. `LocallyOfFiniteType` and `QuasiCompact`
  on the structure morphisms express finite type; `IsSeparated` on both
  structure morphisms and f expresses separatedness.
- `d : Nat` and `SmoothOfRelativeDimension d f` express smoothness of pure
  nonnegative relative dimension. The inherited finite-type and quasi-compact
  instances on f are the inputs of the recorded operation interfaces.
- `Cat E W` is precisely `finiteTorConstructibleIntegralCategory C.l E.val W`,
  with derived completeness, constructibility, and one Tor interval for all
  positive reductions. No category is replaced by a private predicate.
- `ambientSource` is actual `integralDerivedPullback`, followed by
  `integralComplexTwist` and shift by `2 * (d : Int)`. `source` restricts this
  functor through the existing full inclusions, taking only its membership
  proof from reconstruction. No purity isomorphism is selected by this def.
- `operation` is the recorded exceptional/compact-support adjunction of
  `ConstructibleExceptionalCoefficients.System`, at the canonical
  compactification and the integral coefficient stage. `target` has its G.
  The package S is existential in the main theorem, not an additional
  hypothesis and not a choice from an unconstrained existence proof.
  `Data.targetRealization` explicitly identifies G with the project's
  `integralExceptionalInverseImage` on the full finite-Tor category.

### Each conclusion and equation

- `Data.sourceAdditive`, `sourceExact`, `sourceLinear`, `targetExact`, and
  `targetLinear` give the stated exact O_E-linear H and G. Additivity of G
  is already part of the recorded operation. `coefficientLinear` is the
  inherited constant-section action, `Linear.fullSubcategory`, and is not
  a different O_E action.
- `ordinary E F h W` is `integralOrdinaryDerivedScalar` along the actual
  completed coefficient inclusion `IntermediateField.inclusion h`.
  It is ordinary derived tensor, rather than a tensor on an arbitrary tower.
  `ScalarClosed` asserts precisely preservation on W=X,Y; its witness is a
  conclusion `Data.scalarClosed`. `scalar` restricts this ordinary tensor.
  `Data.scalarAdditive` and `scalarExact` give exactness of these functors.
- `scalarBridge` is the canonical completion comparison
  `scalarCompletionIso`, followed by the inverse of the existing
  `System.ring.integralScalar_eq`. The latter system's
  `integralScalar_normalized` identifies its ordinary-tensor realization
  with the recorded `completedScalarComparison` chi. Thus the bridge uses
  the prescribed strict-tower comparison, not an arbitrary endpoint iso.
- `Data.gamma` is a single family of natural isomorphisms indexed by every E.
  Each has components for every object K of the full finite-Tor category;
  naturality is included in `NatIso`. The components are morphisms of the
  existing O_E-module derived categories, so naturality for the O_E-linear
  functors is the stated linear natural transformation.
- `Data.finiteReductions` uses exactly `purAdicSourceReduction`,
  `purAdicTargetReduction`, and `purAdicFiniteArrow` from reconstruction.
  Its reduced map is gamma followed by `targetRealization`; it asserts the
  two canonical reduction identifications are isomorphisms and states
  exactly reconstruction's quotient-linear equality, at every level n+1.
- `Data.a` and `Data.aCanonical` specify the canonical source comparison.
  `sourceScalarComponent` first moves the shift through ordinary scalar
  tensor; it conjugates `integralTwistCompletedBeta` and
  `scalarPullbackCompleted` by the actual `scalarCompletionIso` maps.
  The pullback object is the recorded `constructibleIntegralPullback`.
  Membership/completeness proofs do not select new data.
- `Data.c` and `cCanonical` transport the existing normalized compact-support
  comparison `compactComparison` through `scalarBridge` at X and Y.
  That comparison is `System.ring.comparison.q`, canonically normalized by
  `comparison_normalized` against `PurCompactSupport.comparison` and the
  recorded left realizations. Its direction is C_Y P_E -> P_F C_X.
- `Data.b` is a natural isomorphism C_X G_E -> G_F C_Y. `bMate` explicitly
  applies the F_F-adjunction Hom equivalence to c^{-1} at G_E K followed by
  C_Y of the actual counit. The domains and direction are exactly the
  typed composite in the node, so b cannot be chosen arbitrarily.
- the first conjunct of `Data.coherence` is C_X(gamma_E) followed by b equals a followed by
  gamma_F at C_Y K, for all E,F,h,K. Since all four arrows are components
  of natural transformations, this is their equality of transformations.
- `scalarUnit` is the actual ordinary tensor multiplication unit, lifted
  through the full inclusion. the second and third conjuncts of `Coherence` are precisely the identity
  comparisons after those endpoint unit identifications, including F=E.
- `associator` is the actual `integralOrdinaryDerivedScalarComp`, restricted
  through the full inclusions. the fourth and fifth conjuncts of `Coherence` state the
  two displayed alpha equations, in Lean's left-to-right composition order.
- `sourceShift`, `targetShift`, and `scalarShift` retain the canonical
  individual functor shift comparisons. the sixth and seventh conjuncts of `Coherence` use the existing
  Mathlib `NatTrans.CommShift` predicate, with the canonical composite shift
  structures passed explicitly through `composeShift`. This includes the
  shift-by-one equations of the node. the eighth conjunct of `Coherence` gives
  shift compatibility of the chosen purity maps. Consequently the purity
  square is compatible with the stated units, associators and shifts.

### Recorded dependencies used

- `Sheaf.Paper.PurityFiniteSetting`: `FiniteFieldDatum`, `CoefficientDatum`.
- Mathlib smooth/finite-type/separated morphism interfaces:
  `SmoothOfRelativeDimension`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsSeparated`, scheme `Over` and morphism `IsOver`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `integralSheafTwist`, `sfIntegralTwistingFunctor`;
  `Sheaf.Paper.AdicPurityObjects`: `integralComplexTwist`.
- `Sheaf.Paper.PurAdicReconstruction`: `purAdicReconstruction`;
  its public source/exceptional reduction modules supply
  `purAdicSourceReduction`, `purAdicTargetReduction`, `purAdicFiniteArrow`.
- `Sheaf.Paper.FiniteTorAmplitude` (also exposed by
  `Sheaf.Paper.FiniteTorAmplitudeSites`):
  `finiteTorConstructibleIntegral`, `finiteTorConstructibleIntegralCategory`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`;
  the existing predicate includes `IsSfDerivedComplete` and the normalized
  DVR reductions, as prescribed by `Sheaf.Paper.NormalizedDVRTower`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, its operation/adjunction,
  scalar realizations and normalized compact-support coefficient mates;
  `Sheaf.Paper.IntegralExceptionalInverseImage`:
  `integralExceptionalInverseImage`, `integralExceptionalCompactification`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` through the system realization;
  `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarComparison` through its normalization.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` and
  `Sheaf.Paper.QcqsCompactSupportRealization` supply the actual completed
  rings and compact-support realization used by the normalized system.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionIntegers`, finite coefficient rings;
  `Padic.FiniteCoefficientFields` is the existing index type.
- `Sheaf.Paper.DerivedPullbackTensorHom` and the recorded integral derived
  operation modules: `integralDerivedPullback`,
  `constructibleIntegralPullback`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` supplies the
  recorded ordinary derived change-of-rings framework.
- Mathlib: `Functor.Linear`, `Functor.Additive`, `Functor.IsTriangulated`,
  `Functor.CommShift`, inherited triangulations and `ObjectProperty.lift`.
- Additional existing canonical-map interfaces used to express this node:
  `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `integralOrdinaryDerivedScalar`, `scalarCompletionIso`,
  `scalarPullbackCompleted`; `integralOrdinaryDerivedScalarComp` and
  `integralOrdinaryDerivedScalarUnit` from its scalar-composition imports;
  `Sheaf.Paper.IntegralTwistDerivedScalarCanonical`:
  `integralTwistCompletedBeta`; `Sheaf.Paper.SfIntegralConstructibleLinear`:
  `sfIntegralCoefficientLinear`; `Sheaf.Paper.TwistPreservesFiniteness`:
  `twist_preserves_finiteness`, only for the completeness proof in the
  canonical source comparison.
- Stated proof dependencies are imported: `AdicScalarTraceCoherence` and
  `AdicProjectionShiftCoherence`. The latter is a public import because its
  public unbundled finite-Tor triangulation and canonical integral shift
  interface are also used in the statement's full-subcategory shifts. The remaining three new proof nodes are
  not yet recorded as Lean declarations. The theorem docstring retains all
  four current DAG proof steps and identifies those prerequisites.

### Edge cases and searches

The base field and equal inclusions are retained (`h : E <= F` rather than a
strict inequality). The units and associators are the multiplication maps,
so E=F=L remains covered. No nonzero K or nonempty X,Y hypothesis occurs:
zero complexes and empty schemes are included. d=0 gives twist zero and
shift zero. Reduction index n=0 means quotient exponent 1, never the zero
coefficient ring. Ramified extensions are all included through the existing
completed coefficient map; there is no exponent divisibility assumption.
There is no equality imposed between independent site universes: all objects
use the recorded common purity universe, including its small pro-etale sites.

Searches performed before defining the helpers:
- msearch.py leanfinder, query "Adic smooth purity isomorphism natural in
  constructible complexes compatible with finite extension of coefficient
  fields": eight results about period rings/formal smoothness; none is a
  coefficient-natural adic purity statement.
- msearch.py loogle, query `"purity"`: twelve compiler/effect-purity results,
  no mathematical purity comparison.
- msearch.py grep, query `purity.*scalar|scalar.*purity|smoothPurity`: zero
  Mathlib hits.
- rg on the project's `lean/WeilConjectures` and `lean/Sheaf` for
  `purity.*scalar|scalar.*purity|smoothPurity`, and for the exact item id:
  existing finite-purity and comparison ingredients, no existing declaration
  of this simultaneous coefficient-natural family.
- Focused rg/source reads found the recorded reconstruction, normalized
  exceptional coefficient system, actual ordinary scalar associator/unit,
  completion comparison, completed twist beta and completed pullback map;
  these are reused instead of copied or replaced by arbitrary maps.

No new independent notions or dependency repairs were needed. There is no
STATEMENT-DISPUTED assertion. The sole sorry is the main theorem, matching this
node and accompanied by its complete four-step natural-language proof plan.

### Validation

Every compiler invocation used the prescribed scompile.py server wrapper.
Initial import probes compiled. Elaboration checks caught coefficient-stage
inference and composite-shift instance issues; the final predicates pass
the canonical shift structures explicitly. Final compile and delivery
preflight results are recorded by the delivery wrapper.

An earlier delivery dry run passed at commit 485887cca5d. The repaired packet
is being revalidated against the current published library.


### Returned H3 repaired (head 0ce062219a14)

The saved delivery left `Data.targetRealization` free: the old
`finiteReductions` constrained only its composite with `gamma`. The repair adds
`targetReductionMap` and `Data.targetRealizationReductions`. For every E, K and
n, reduction of the realization followed by the exact existing
`purAdicTargetReduction` now equals `targetReductionMap`.

That helper contains real data: inverse X scalar realization, followed by the
System integral-to-finite `comparison.b`, followed by `finiteRight` at the
canonical compactification, followed by the actual finite exceptional functor
applied to the Y scalar realization. Its codomain is explicitly the very
`purAdicFiniteArrow.right` used in reconstruction. The System's
`finiteScalar_normalized` pins these scalar realizations to the actual reduction
functors, and `comparison_normalized` pins its compact-support mate. The next independent return correctly found that this equation alone was
insufficient: finiteRight was itself a bare, unnormalized isomorphism. The current
repair below adds its missing Hom-transpose normalization; the prior argument
that this reduction equation alone removed all freedom was incorrect.
`finiteReductions` and `puritySquare` still use the same `gamma` field.

The finite-level formula includes n=0 (exponent 1), all finite fields E, all K,
and the empty schemes and d=0. The scalar unit, composition, shift and source
normalizations checked OK by the return are retained. This repairs the Lean
encoding of the existing statement; no node statement is changed. The live
node still has `lean: null`; the saved node differs from it only in `lean`.

### Self-check of the repair

Read the item, its proof, the finite-reduction interfaces, and the full
System scalar, comparison and finiteRight signatures. Checked the composite's
direction at every endpoint: actual reduction of G_E K to the full finite-Tor
scalar image, then the finite G_n image, then the intrinsic finite exceptional
image of actual K_n. This is precisely reconstruction's target, rather than a
new endpoint or arbitrary comparison. No new theorem or sorry is introduced.
The sole postponed theorem remains `adicPurityScalarNaturality`.

### Current-library elaboration repair

The saved packet's new target-reduction helper did not infer the System ring
stages from their coefficient objects. Explicit integral and finite stages and
their scalar shift instances now fix those indices. Reading the resulting
composite also exposed the two distinct universal derived-tensor presentations:
System reduction uses `Scheme.pbcDerivedExtend`, while reconstruction uses
`scalarReductionDerivedExtension`. They are canonically isomorphic, not
interchangeable by definitional reduction.

`reductionBridge` is real data constructed by `Adjunction.leftAdjointUniq`
from `derivedScalarExtensionRestrictionAdjunction` and the normalized
`Scheme.pbcDerivedScalarAdjunction`, both to the same exact scalar restriction.
It then removes the identity quotient cast in `PurCompactSupport.projection`.
The target reduction composite uses this bridge at X, and its inverse inside
the finite exceptional functor at Y. Thus its domain and codomain are exactly
the reconstruction reductions requested by H3, with every intervening arrow
still the System's integral-to-finite mate and `finiteRight` realization.
This adds no arbitrary comparison, no new theorem, and no new sorry.

### Resumed repair validation (2026-10-22)

The required initial dry run found a stale extra `d` argument in the new
`targetReductionMap` application, and local irreducibility of `source` and
`target` hid the endpoint identifications in `finiteReductions` and `bMate`.
Removed that unused argument and retained transparency of those two endpoint
functors; no mathematical field or equation was removed. The prescribed
scompile.py then compiled both the sandbox module (51.2 seconds) and its actual
library module path (58.1 seconds) cleanly, within the fixed 60-second limit.
Compared the saved node with the current shared node: only `lean` differs.
The repair equation still pins the target realization independently of gamma,
and the finite-reduction equation and scalar square still share that gamma.


### Returned H3 repaired (immutable head 27ff45d282d6)

The return identifies exactly the remaining freedom in `S.ring.finiteRight`.
It is a bare isomorphism in RingSystem, so the preceding reduction equation
alone permits a coefficient-dependent automorphism to absorb a change in gamma.
The present repair retains every existing clause and adds
`Data.finiteRightNormalized`, a conclusion rather than a new hypothesis.

`FiniteRightNormalized` requires the finite right realization, in the fixed-scalar
coordinates, to identify the System Hom transpose with the ordinary étale
compact-support/exceptional Hom transpose. It quantifies over every positive
level, every finite coefficient field, every finite-Tor source and target, every
bounded-below étale representative of the source, every isomorphism realizing
that representative and every map from the System compact support to the target.
This is the Hom-transpose form of the counit mate required by the return.

`finiteLeftFixed` contains real data: System.ring.left, the existing
`constructibleFiniteImageIso`, the canonical realization counit, the existing
`sfIntrinsicCompactSupportComparison`, and the realization unit.
`finiteRightFixed` contains real data: System.ring.finiteRight transported by
the canonical realization equivalence and its inverse unit. The right-hand side
of the equation uses `fixedCompactSupportComparisonIso` and
`derivedComparisonAdjunction` followed by the actual
`Etale.rightDerivedUpperShriekAdjunction`, at the same compactification instance
as `sfFiniteExceptional`. None of these comparisons is newly selected.

Every finite-Tor input has a bounded-below étale representative. Full faithfulness
of comparison pullback and of the intrinsic realization makes the displayed
Hom equation determine every finiteRight component uniquely (Yoneda). In
particular take the source to be the finite right image and the map to be the
System counit: its transpose is the identity, so the equation fixes finiteRight
itself. Multiplying it by a unit while fixing the adjunction violates the equation.
If an adjunction presentation is changed by conjugacy, the equation changes its
right realization by exactly the same conjugacy; it cannot independently alter
the finite reductions of the purity map in the intrinsic exceptional functor.
The reduction bridge, target-realization reductions and all scalar equations
therefore now refer to the same normalized exceptional operation.

Additional searches in this repair:
- msearch.py leanfinder: "Comparison between right adjoints is uniquely determined
  by its Hom transpose under the same normalized left adjoint" returned
  `Adjunction.rightAdjointUniq` and its unit/counit and composition identities.
- msearch.py loogle: `Adjunction.rightAdjointUniq` returned unknown identifier,
  zero hits; the fully qualified declaration was found by LeanFinder and grep.
- msearch.py grep: `rightAdjointUniq|homEquiv.*naturality` in
  `CategoryTheory/Adjunction` returned 25 matches, including Unique.lean:102.
- Focused source reads in the shared Sheaf and WeilConjectures trees found the
  canonical finite image and realization comparisons and the existing normalized
  finite comparison-class Hom formula. No new independent notion or DAG node is
  needed: these are helper definitions of the item's already specified adjunction
  comparison, recorded in lean.declarations.

The equal-coefficient, zero complex, empty-scheme and d=0 cases are retained.
The normalization is imposed for n : ℕ+, including exponent 1. The representative
quantifier is over the existing small étale site with ModuleCat.{u+1}, with the
canonical ULift of the actual finite quotient ring. No site universes are equated.
No new theorem, proof, or sorry is introduced.


### Final resumed self-check (2026-10-23)

The required first dry run of the retained packet found a real 60-second timeout
and leftover profiler-option warnings. Removed development profiling. The profile
showed expensive cleanup of the normalized adjunction and repeated kernel checking
of the dependent Data record. Disabled optional let-to-have cleanup, and named the
unchanged finite-reduction proposition `FiniteReductions` and unchanged coefficient
counit-transpose proposition `CoefficientMate`. Data.finiteReductions and Data.bMate
now refer to those exact propositions. These are helper definitions of this node,
with real proposition bodies, rather than additional hypotheses or postponed lemmas.
The helpers allow source and target functors to remain opaque while checking Data;
their mathematical definitions, endpoints and all equations are unchanged.

Re-read the immutable-head return and the current RingSystem fields: finiteRight
still has no normalization upstream. Checked finiteRightFixed against the actual
definition of sfFiniteExceptional as inverse realization, sfFiniteExceptionalFixed,
then forward realization. The final inverse unit in finiteRightFixed has exactly
the required source and target. Checked finiteLeftFixed against constructibleFiniteImageIso
and sfIntrinsicCompactSupportComparison; its last inverse unit removes forward-then-
inverse realization. In FiniteRightNormalized, the inverse fixed compact-support
comparison takes an etale compact-support image into the pro-etale compact-support
image; the inverse finiteLeftFixed then reaches the System compact support. The
derived site-comparison transpose followed by the etale exceptional transpose and
comparison pullback has the same target as finiteRightFixed. This is precisely
the previously missing adjunction normalization, not an endpoint isomorphism.

The finite-Tor category consists of bounded constructible etale-origin objects.
Hence the bounded-below representative quantifier does cover each M; taking
M = O.G.obj N and v the counit fixes the finiteRight component. This rules out
the unit-per-field modification identified in the return. All scalar equations
and reductions still involve the same gamma. No additional sorry occurs.

Compared the current shared node and the sandbox copy: only lean differs.
The current main-20261015 purity unit explicitly requires the counit-compatible
comparison and coefficient compatibility. No source or DAG statement correction
is needed. This self-check is by the assigned worker; no additional agent was
started, as the dispatcher's repair brief requires.

The final compilation refactor also names `TargetRealizationReductions` and
`Coherence`. Data.targetRealizationReductions retains the identical quantified
reduction equation through the former. Data.coherence asserts all eight former
fields as an ordered conjunction: puritySquare, aUnit, bUnit, aComposition,
bComposition, aShift, bShift, gammaShift. No quantifier, component, shift structure,
or equation was removed. Grouping the equations avoids repeating the large
dependent record context in generated projections. All helpers are recorded in
lean.declarations. The final scompile.py run passed both sandbox and library
module checks, with the library-path compilation reported at 50.5 seconds.

## Second reading by Q111

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
