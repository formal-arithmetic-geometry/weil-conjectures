## Worker report

Current worker repair of the H3 return on immutable head `24d3ed97d8f8`:
previous finding 2 is now rendered explicitly by
`CoefficientDerivedSystemFibers.fiber_transition`. The retained sandbox was compared
with the current shared main node: only `lean` and the four previously delivered new
`stmt_deps` differ. The node's mathematical statement, source, proof and other fields
are unchanged. The prescribed delivery wrapper rebases the delivery on current main.
The historical review and validation entries below describe earlier heads; they do
not constitute a second reading or validation of this new transition repair.

The new field quantifies over actual systems `M N`, their normalization witnesses,
and every `h : n ≤ m`. Its left side is
`coefficientSequenceTransitionAdjoint ... h (coefficientSequenceInternalHom.obj (op M,N))`
followed by `(fiberHom M N hM hN n).hom`. Its right side first applies finite quotient
extension to `(fiberHom M N hM hN m).hom`, then applies
`coefficientFiniteQuotientHomComparison ... h M_m N_m`, and then
`coefficientFiniteInternalHom.map (alpha_M.inv.op, alpha_N.hom)`. Both alphas are
`coefficientSequenceNormalizationIso`, defined from the actual transition-adjoint
of `coefficientSequenceDerivedTransition` and the finite quotient adjunction.
Thus the equation states exactly the missing scalar-extension transition clause,
including both input normalizations and the original horizontal restriction.

The finite quotient helpers specialize the recorded
`SheafOfModules.derivedChangeOfRingsIndependentCoefficients` in
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` to the actual
`normalizedDVRQuotient` in `Sheaf.Paper.NormalizedDVRTower`, retaining its
commutative structure. `coefficientFiniteQuotientDerived` and
`coefficientFiniteQuotientCounit` are the universal derived pair from that witness;
`coefficientFiniteQuotientModel` uses that very counit on K-flat representatives.
No unrelated scalar-extension functor or comparison is introduced.

`CoefficientFiniteQuotientCalculus.ordinary_unit` fixes the ordinary adjunction
by the actual sheafification unit and `ModuleCat.extendRestrictScalarsAdj` formula
`x ↦ 1 tensor x`. `unit_model` fixes the derived adjunction by that ordinary unit
and the universal derived counit. `tensor_model` fixes its derived tensor comparison
on every pair of K-flat representatives: the chain isomorphism sends the actual
extended pure-tensor generator to the tensor of the extended generators, and the
localization square uses the recorded K-flat model isomorphisms on both sides.
Those generators uniquely determine the chain map. Consequently the new
`coefficientFiniteQuotientHomComparison` is precisely c_(m,n), the transpose of
reduced finite evaluation through this normalized tensor comparison; it uses the
existing `coefficientBaseChangeHom` definition, not an independently chosen map.

The new postponed theorem
`coefficientSequenceTransitionAdjoint_isIso` is a named part of the item's existing
normalization clause and proof steps 5/10. Its docstring gives the complete proof:
the adjunction identifies precomposition by the adjunct with
`f ↦ tau >> Res.map f`; the existing normalization gives its bijectivity for every
target, and Yoneda detects invertibility. The additional named theorem `coefficientFiniteQuotientCounit_isIso` states the
K-flat counit clause of that very recorded change-of-rings witness; its docstring
gives this specialization as the complete proof. All definitions have real construction
data or use the recorded universal derived pair. Helpers belong to the existing
calculus notion and are listed in `lean.declarations`; no extra independent notion
or dependency-module repair was required.

Edge cases for this repair: `m = n`, the first positive level `n = 0`, zero systems,
zero complexes, the empty scheme, and arbitrary unbounded inputs remain included.
Neither the Hom system itself nor its transition is assumed normalized or invertible;
only M and N carry the node's normalization hypotheses. No flatness of B_m → B_n
or new universe equality is imposed: the site retains object/morphism sizes t+1/t
and coefficients/modules max(u,t+1).

Fresh searches for this repair: LeanFinder query "Derived scalar extension of
internal Hom is the transpose of reduced evaluation, compatible with normalized
inverse coefficient-system transitions" returned eight ordinary module-Hom and
extension/restriction declarations, none the requested derived system identity.
Loogle `ModuleCat.extendRestrictScalarsAdj` returned six ordinary scalar-adjunction
hits; its unit is used in the ordinary representative normalization. Mathlib grep
`derived.*[Hh]om.*[Cc]omparison|[Cc]omparison.*derived.*[Hh]om` in CategoryTheory
returned zero hits. Source searches in upstream WeilConjectures and shared Sheaf
for the new helper names and `fiber_transition` found no existing declaration.
The existing constant-coefficient `CoefficientEvaluationDerivedLeftAdjoint` was
inspected: it supplies an ordinary general-site tensor, but not this recorded
finite-quotient derived pair or the missing normalized Hom transition identity.
Search outputs are in searches.jsonl. The previous three-kind searches and full
clause/hypothesis inventory remain below; clause 7's previously implicit transition
claim is superseded by the explicit field described here.

Compilation repair: the first full calculus check timed out at 60 seconds; a
subsequent diagnostic also timed out compiling the retained tensor-Hom module.
The large representative formulas are now named propositions within the same
owning modules: `CoefficientTensorUncurryModel` is exactly the previous
`uncurry_model` formula, and `CoefficientFiniteQuotientTensorNormalization` is
exactly the new quotient tensor model formula. The structure fields assert those
same propositions. `CoefficientFiniteQuotientData` holds the quotient data;
`CoefficientFiniteQuotientCalculus` extends it with the ordinary-unit, derived-unit
and representative tensor propositions. `CoefficientFiniteQuotientOrdinaryUnit` and
`CoefficientFiniteQuotientDerivedUnit` package the unchanged unit formulas once. These packaging changes reduce repeated kernel
checking of generated structure constructors/projections without altering any
mathematical clause or adding a module. Primary signatures stay verbatim.
The new `coefficientSequenceNormalizationIso` and quotient Hom comparison have
explicit result types, and the quotient K-flat counit computation uses the named
`coefficientFiniteQuotientCounit_isIso` theorem. All helper declarations are in their
owning nodes' `lean.declarations`.

The ordinary-unit predicate now names `coefficientFiniteQuotientUnitSection`,
whose real data is the same sheafification of `1 tensor x` with the recorded
change-of-rings object equality. The derived-unit predicate uses the equivalent
complex-localization equation at `DerivedCategory.Q.obj P`, the canonical
`coefficientFiniteQuotientModel`, and the exact restriction factorization. Conjugating
by the natural `DerivedCategory.quotientCompQhIso` gives exactly the homotopy-category
unit/counit equation used earlier; the model was defined from that very counit.
Thus both representative normalizations fix the same maps and impose the same
condition, while avoiding repeated reductions of the homotopy quotient in the
structure's generated declarations.

A low-budget scratch diagnostic located the remaining kernel cost in the actual
section-unit constructor and the quotient tensor-normalization predicate. The
recorded object equality is now exposed as the named theorem
`coefficientFiniteQuotientExtension_obj` (proof plan: take the object-equality
component of the same recorded change-of-rings witness), and the section-unit
constructor uses that explicit equality. The tensor-generator normalization uses
this actual section-unit constructor directly. Under `ordinary_unit` this is the
same generator equation as the adjunction-unit form; it fixes the canonical pure
tensors even before using that equality. The transition-adjoint helper's implicitly
used tensor-data parameter is named `_S` to avoid the unused-variable warning.
Scratch diagnostic options are absent from every delivered module.

Current resumed repair additionally factors the ordinary section-unit construction through
`coefficientChangeOfRingsUnitSection`, a general-site formula using the actual ordinary
module scalar-extension unit and sheafification unit. The finite-quotient specialization
then applies only the recorded object-equality transport. Its result type is the unchanged
underlying section object before scalar restriction; restriction changes only the action.
This avoids repeatedly checking the expanded coefficient-ring constructions, and preserves
both the pure-tensor generator equation and the ordinary-unit normalization. The helper
is part of this calculus, has real data, and is listed in `lean.declarations`.
The general section-unit helper now uses `CategoryTheory.toSheafify` directly on the
underlying abelian presheaf. Mathlib's
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app` identifies this
map definitionally with the underlying module-sheafification unit previously used.
`CoefficientScalarTensorGenerators` packages verbatim the pure-tensor generator formula
over general source/target ring sheaves, one scalar-extension functor and its section-unit
function. The quotient tensor normalization specializes it to the recorded extension
and actual unit, for the same chain isomorphism appearing in its localization square.
No formula or quantifier has been removed. The ordinary-unit equality explicitly applies
`coefficientRestrictionSection`, the identity on the underlying section, before comparing
it to the extension section. This exposes the unchanged element without repeatedly
unfolding the concrete restricted scalar actions. Its general-site definition is `x ↦ x`.


Fresh supporting searches in this resumed pass: Loogle found
`PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`, used to justify
the direct `toSheafify` formula; LeanFinder found the same sheafification infrastructure.
LeanSearch for the normalized derived Hom scalar-transition comparison found only
ordinary extension/restriction and linear-dual transpose declarations. Mathlib grep of
CategoryTheory for derived-Hom comparisons found no match. These do not already state
the quotient transition identity; all search records are retained in `searches.jsonl`.

The fresh comparison with shared main also restored its unchanged `lean_audit` field
in the sandbox copy; outside `lean`, only the four authorized new statement dependencies
differ from main. Historical second readings have been relabelled explicitly: the second
reader must review this repaired version independently.

Current repair validation is recorded at the end after the fresh wrapper runs.


This resumed worker pass reviewed the complete module against the current node,
its eighteen statement dependencies, and its fifteen proof steps. The main theorem
`WeilConjectures.coefficientDerivedSystemEvaluationCalculus` asserts existence of the full
`CoefficientDerivedSystemCalculus` together with `CoefficientDerivedSystemCoherence`.
All theorem proofs remain `sorry`; definitions have real data or use uniquely characterized
objects. The DAG statement is unchanged. The item changes only `lean` and adds the new
definition nodes below to `stmt_deps`.

This repair addresses the maintainer's H3 return on immutable head `97f7054c2b81`.
That return supersedes the historical second-reading verdicts: the comparisons
were not sufficiently normalized and the old degree-zero clause did not mention gamma.
The returned constructions and full clause inventory are retained, with the following
substantive repairs in this module (not an unchanged re-push):

- `coefficientTensorGenerator` uses the actual sheafification unit, ordinary module tensor,
  and total-complex summand inclusion. `coefficientScalarTensorIso_exists` uniquely fixes
  scalar extension's tensor comparison by `eta(x tensor y) -> eta(x) tensor eta(y)`.
  `coefficientEvaluationTensorIso_exists` uniquely fixes evaluation by preserving the
  very same local pure tensors. These are chain isomorphisms, not arbitrary derived isos.
- `CoefficientTensorModels.comparison` now comes with `uncurry_model`: under this
  comparison and the recorded Hom localization factorization, the closed adjunction
  is the chain-level formula `x tensor y -> phi(x)(y)` into the fixed K-injective
  replacement. `coefficientHomComponent` is the actual chosen product projection.
  It and the fixed Hom representative evaluation are extracted without changing their
  data to `CoefficientHomRepresentativeEvaluation`, so each file remains within the
  compilation limit without relaxing that limit.
  `coefficientHomResolutionIso` is the actual `Localization.fac`, and
  `coefficientHomResolutionInverse` is the inverse of its localized augmentation.
- `CoefficientFiniteTensorNormalization` and `CoefficientEvaluationTensorNormalization`
  identify the derived comparisons with those ordinary chain isomorphisms on K-flat
  representatives. `CoefficientTensorModels.uncurry_model` additionally gives the
  direct evaluation composite on the same representative comparison, fixing the
  counit normalization and excluding a simultaneous sign twist. `CoefficientReductionTensorNormalization` requires one simultaneous
  strict-system chain map, all its actual quotient-transition equations, its normalized
  finite components, and its equality with `reductionTensor` BEFORE evaluation.
  `CoefficientReductionTensorEvaluation` gives the exact comparison square with rho.
  These four requirements are fields of `CoefficientDerivedSystemFibers`.
- `coefficientGammaZero` is H⁰ of gamma itself. `coefficientGammaZeroMap` is its composite
  `gamma.hom >> coefficientMappingProjection >> globalEvaluation.hom`.
  `CoefficientHomProjection` uses `coefficientGammaZeroMap`, which explicitly composes
  H⁰(gamma) with H⁰ of the actual projection
  and fiber identification, and applies the finite Hom identification to its value,
  takes the inverse integral Hom identification of h, and equates it with
  `rho_P >> finiteExtension.map h >> rho_(L N).inv >> eval(counit_N)`.
  Thus it states the actual degree-zero gamma projection, not just an unrelated
  scalar-adjunction formula.
- The Hom identifications themselves use `coefficientHomZeroEquiv_exists`, uniquely
  normalized by taking each represented zero cycle to its actual chain map in the
  derived category. `coefficientHomZeroClass` uses the universal derived-sections unit
  and the fixed Hom localization factorization; `coefficientHomZeroEvaluation` uses
  the real Hom-product projections. No arbitrary sign choice of additive equivalences
  is hidden in the new identity. These normalize the recorded RHom comparison rather
  than define a replacement cohomology theory.

The existing eighteen dependency records are used without change. The item's
`lean.declarations` lists its remaining helper declarations. The extracted canonical Hom evaluation, zero-cycle class and ringed sequence site are recorded in the
new definition nodes described below; the item adds these four nodes to `stmt_deps`. There are no dependency-module deliveries.
The sandbox item was compared with the current shared node: outside `lean`, only these four
new statement dependencies were added.
The validation section below records the final compile and dry-run results.

Clause inventory and matching Lean (all verdicts refer to the repaired module):

1. Objects: a prime ell, finite extension E/Q_ell, its valuation ring and positive
quotients, and an arbitrary scheme W. The section binders are `l`, `[Fact l.Prime]`,
`E`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]`, `W : Scheme.{t}`.
The valuation ring, chosen uniformizer, coefficient quotients and completed coefficient
sheaf are those of `integralCoefficientCommRingSheaf` and
`completedIntegralCommRingSheafUnrestricted`, not replacement ring variables. Verdict: exact.
2. Site and sizes: `Scheme.ProEt.topology W` is the recorded small pro-etale site, with
object universe t+1 and arrow universe t; coefficients/modules have universe max u (t+1).
`coefficientSequenceTopology` uses its actual product with the ordered natural numbers.
`coefficientSequenceCommRingPresheaf` uses the recorded coefficient quotient maps.
`coefficientSequenceModules` is modules over that ringed sequence site. Vertical
restrictions are the ordinary module sheaves; horizontal restrictions are the specified
semilinear quotient transitions. Its sheaf condition is precisely componentwise. Verdict: exact.
3. Ordinary unbounded derived categories, exact evaluations, restriction U, and L:
`coefficientSequenceDerived`, `coefficientSequenceDerivedEvaluation`,
`coefficientSequenceDerivedRestriction` and `coefficientSequenceLimit` use the ordinary
localizations and actual exact module functors. L is the total right-derived ordinary
limit after U, with the recorded K-injective model, not a tower of derived objects.
`coefficientSequenceProjection` is U followed by the actual normalized total-limit
projection and the canonical restriction/evaluation identification. Verdict: exact.
4. Normalization: `IsNormalizedCoefficientSequence` says precomposition with the
actual transition gives a bijection into every restricted target. By the recorded
extension/restriction adjunction and Yoneda this says precisely that its derived
transition-adjoint is invertible for every n <= m. It does not assume invertibility
of the underlying scalar-restricted transition. Verdict: exact.
5. Reduction is a FUNCTOR and is canonically computed on ONE flat-term K-flat
representative: fields `reduction`, `reductionEvaluation`, `reductionModel` in
`CoefficientDerivedSystemCalculus`. `CoefficientReductionModels` uses one strict
complex C with all its level comparisons; its chain-level equations compare the
actual transitions with `coefficientOrdinaryQuotient`. The latter is the unique
ordinary scalar-adjunction quotient map, and `coefficientFiniteReductionModel`
uses the recorded derived-change-of-rings counit. No arbitrary tower maps or
independent choice of representatives at different levels occur. Verdict: exact.
6. Derived adjunction, reconstruction unit, counit and both triangles:
`adjunction : reduction ⊣ coefficientSequenceLimit ...` contains the triangles.
`unit_projection` and `counit_projection` fix the actual finite maps using
`coefficientFiniteAdjunction`, defined to be the existing unit-normalized scalar
adjunction itself. `reduction_normalized` supplies the stated normalized reductions.
No field asserts that the reconstruction unit is invertible. Verdict: exact.
7. Functorial simultaneous internal Hom: `coefficientSequenceInternalHom` is the
recorded actual `derivedInternalHomOfUniverses` on the ringed sequence site.
`systemClosed` equips this very bifunctor with tensor-Hom evaluation and transposition;
`systemTensorModel` identifies its tensor with total tensor on K-flat representatives.
`fiberHom`, `fiber_evaluation`, and `fiber_naturality` identify its fibers with the
recorded finite internal Hom on normalized inputs. The repaired `fiber_transition`
explicitly equates the actual internal-Hom transition-adjoint, transported by
`fiberHom` at m and n, with c_(m,n) followed by RHom(alpha_M inverse, alpha_N).
`coefficientFiniteQuotientHomComparison` defines c_(m,n) by reduced evaluation and
transpose; `quotientCalculus.tensor_model` fixes the quotient tensor comparison on
K-flat representatives by the actual pure-tensor chain formula. Verdict: exact.
8. Derived tensor, beta, and its three compatibilities: `integralTensorModel`,
`systemTensorModel`, `finiteTensorModel`, `reductionTensor`, `finiteTensor`, and
`evaluationTensor` use the actual total tensor on the existing K-flat subcategories.
`coefficientBaseChangeHom` is defined by reducing evaluation and transposing.
`reduction_compatible` supplies naturality, transpose and internal composition as
SYSTEM equations; `beta_evaluation` identifies its finite evaluation with the usual
finite evaluation-defined comparison. P,Q are unrestricted ambient derived objects.
There is no beta-isomorphism field. Verdict: exact.
9. A system map is invertible iff all evaluated maps are: `isIso_iff_evaluations`
quantifies over arbitrary actual system maps. Verdict: exact.
10. Global mapping system H: `coefficientSequenceGlobalHom` is the simultaneous
internal Hom followed by U and total right-derived termwise global sections,
landing in D(Tow(Ab)). `globalEvaluation`, `systemSectionsEvaluation`, and
`globalEvaluation_model` identify its evaluations with the existing finite
`coefficientFiniteGlobalHom` by the internal-Hom fiber map itself. The underlying
functors and `fiber_naturality` give naturality for input derived morphisms.
Verdict: exact.
11. Integral and finite global derived mapping complexes:
`coefficientIntegralGlobalHom` and `coefficientFiniteGlobalHom` are actual
internal Hom followed by `coefficientGlobalSections`, the total right-derived
Hom out of the module unit. This is the recorded rhom-global-sections interface,
not degree-zero Hom substituted for the whole mapping complex. Verdict: exact.
12. Specified enriched gamma for arbitrary P and normalized N:
`coefficientEnrichedAdjunctionMap` is the adjunct of beta followed by Hom of the
counit. `enriched_isIso` makes this particular map invertible; `.gamma` is a REAL
composite of its image under derived sections and `globalLimit`. Its target is
actual `coefficientMappingLimit` of H. `globalLimit_model` fixes the global-limit
comparison by the simultaneous ordinary sections/limit comparison and universal
derived units. Thus the assertion is on resolutions simultaneously. Verdict: exact.
13. Actual gamma projections and their scalar adjunction: `gamma_projection` uses
the specified `coefficientMappingProjection` and the actual `coefficientSequenceProjection`.
Its right side is postcomposition by that projection, the finite enriched scalar
adjunction, the canonical scalar-section transport, and `reductionEvaluation`.
`ordinaryScalarSections_formula` fixes the transport by b*f(1), and
`scalarSections_model` fixes its derived version. `finite_enriched_isIso` says that
the finite comparison is the scalar adjunction isomorphism. Verdict: exact.
14. Degree-zero formula, naturality, units/counits and composition:
`hom_projection` explicitly evaluates H-zero of gamma followed by its actual limit
and finite mapping projections, under the uniquely cycle-normalized integral and
finite Hom equivalences; its value is reduction of h followed by evaluated counit.
`gamma_naturality` gives the two-variable equation. `composition` is the node's
step-15 tensor-parametrized composition identity, using `.tensorLimitMap`, the
REAL counit mate; closed transposition and derived sections give the asserted
mapping-complex composition equation. The adjunction triangles and these equations
include the unit/counit compatibility. Verdict: exact.
15. Quantifiers and nonclaims: the final theorem existentially supplies the entire
`CoefficientDerivedSystemCalculus` and its `CoefficientDerivedSystemCoherence`.
Normalization hypotheses occur on fiber Hom and gamma's N only. No completeness,
boundedness, flat quotient, finite-field structure on W, reconstruction isomorphism,
or arbitrary-input beta invertibility is imposed or asserted. No tensor product of
an integral mapping complex with a finite quotient occurs in gamma. Verdict: exact.

Dependency reading: I checked the signatures and defining data of
`CompletedIntegralCoefficientGerm`/`CompletedIntegralCoefficients`, `NormalizedDVRTower`,
`IntegralReductionTower`, `KFlat` and `KFlatResolutionIndependentCoefficients`,
`DerivedInternalHomOfUniverses`, `RhomGlobalSectionsOfUniverses`,
`RingedSiteZerothHypercohomologyOfUniverses`,
`RingedStrictTowerHomotopyLimitOfUniverses`, and
`DerivedScalarExtensionRestrictionAdjunction`. The last supplies unrestricted
scheme-level coefficient adjunctions, avoiding the auxiliary finite-field datum
of some older integral-tower interfaces. I also read the pro-etale framework size
note and the exact pro-etale derived-category declarations. Typed wrappers `coefficientFiniteDerivedExtension` and
`coefficientFiniteDerivedRestriction` display the existing functors on the recorded
finite categories without changing either construction. The cumulative tensor,
reduction, fiber and coherence structures only divide the statement into manageable
packages. The generic K-injective,
exact-functor, Hom-complex, total-tensor and derived-adjunction sources used for the
statement and proof plan are imported. No dependency record needs replacing.

Source reading: Stacks `sites-cohomology.tex`, Tag 06YS (K-flat resolution), the
sequence-site construction and Tag 0941, and Tag 0A95 (well-defined RHom), together
with `injectives.tex` Tag 079P. These concern small ringed sites and unbounded
complexes and add no Noetherian, boundedness, geometric finiteness or characteristic
hypothesis. As the node explicitly says, the enriched varying-coefficient conclusion
is agent-formulated; I compared the full fifteen-step node proof rather than
attributing the whole conclusion to a Stacks tag.

Edge cases: the index is the fixed nonempty positive sequence, not an arbitrary
index set that might be empty; Lean index zero is exponent one. Identity quotient
maps (m=n), zero objects and complexes, arbitrary unbounded complexes, and the
empty scheme are included. No hypothesis excludes W in characteristic ell or
characteristic zero. The field extension is finite as stated; no replacement by
an arbitrary ring or algebra was made. All constructions retain independent site
object/morphism sizes t+1/t and arbitrary coefficient universe u.

Independent searches: LeanSearch query "Derived internal Hom for normalized inverse
systems of module sheaves over quotient rings commutes with evaluation and gives an
enriched adjunction to derived inverse limit" returned ordinary sheaf pullback
adjunctions, presheaf evaluation limits, and light-condensed internal Hom; I inspected
those signatures and none is the node. LeanFinder query "derived category inverse system coefficient
ring internal Hom evaluation adjunction" returned unrelated light-condensed/Hom
and Ext results. Loogle query `CategoryTheory.Adjunction` returned generic
adjunction infrastructure, not this varying-coefficient calculus (an earlier
query mentioning an unknown `CategoryTheory.DerivedCategory` was discarded).
I also used rg with `cartesian`, `semilinear`, `strict`, `sequence`, `evaluation`,
`derived`, `internalHom`, `homotopyLimit`, and coefficient names in Mathlib,
upstream WeilConjectures and this project's Sheaf sources and DAG. In particular
the constant-coefficient equal-universe diagram-site realization and the geometric
compact-support reduction-tower functor are different statements. The DAG's
semilinear derived-sections node has no recorded declaration and does not supply
this calculus. No exact existing declaration was found. Search outputs are retained
in searches.jsonl. The closed-structure and model predicates here are packaging of
this node's conclusions tied to the existing Hom and tensor, not replacement notions.

Mismatches repaired: the first worker's theorem omitted the reduction model and
strict transition equations; finite reduction identifications; normalized image;
unit and counit projection normalizations; simultaneous closed tensor-Hom data;
fiber Hom comparisons and their naturality; beta and all its compatibilities;
joint conservativity; the D(Tow(Ab)) global mapping system; enriched gamma, its
actual projection equations, scalar-adjunction and degree-zero formulas,
composition and resolution normalization. All these are now included. Added the
missing source/blueprint docstring for the evaluation factorization helper and
expanded the main theorem docstring to follow all fifteen proof steps. Retained
correct original constructions. Definitions consist of actual functors, universal
composites or unique characterized maps. Every postponed proposition remains a
named theorem with `by sorry` and a proof explanation. There is no data-valued sorry.

For compilation performance, named equality lemmas identify the actual underlying
abelian section objects before stating the transition equation. Its characterization
is the same horizontal restriction, transported by those equalities, rather than an
implicit reduction of a large scalar-action record. The large final equations are
named proposition definitions; the coherence fields assert those very propositions.
This changes neither their quantifiers nor their maps.


Current searches: `msearch.py` LeanFinder query “Derived adjunction between strict
coefficient-system reduction and total derived inverse limit with fiberwise internal Hom
and normalized projections” returned eight generic derived-adjunction declarations,
including `CategoryTheory.Adjunction.derived` and its unit/counit formulas. They do not
construct the ringed sequence site or its fiber Hom and enriched projection comparison.
Loogle query `"DerivedCategory", "Adjunction"` returned zero hits. The repair query
`HomologicalComplex.homologyπ, DerivedCategory.homologyFunctorFactors` also returned
zero hits; those existing declarations were then read directly in Mathlib. `rg` for the item id,
`coefficientDerivedSystemEvaluationCalculus`, and `CoefficientDerivedSystemCalculus`
in upstream `WeilConjectures`, this project's `lean/Sheaf`, and the upstream-name index
returned no matches. `msearch.py grep` for `derived.*[Ss]ystem.*[Ee]val|[Ss]ystem.*[Rr]eduction.*[Ll]imit`
in Mathlib CategoryTheory and the corresponding full-Mathlib `rg` search returned no matches. Earlier detailed search outputs remain
in `searches.jsonl`.

Four new definition nodes are described below. There are no dependency modules,
statement corrections, or disputed statements.

Validation from the previous returned version is historical and does not validate this
repair. Fresh verification for the retained H3 repair is recorded below.

Recorded dependency interfaces used (module / declaration):

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` / `Padic.finite_coefficientExtensionRing`;
  its public imports supply the actual finite-extension valuation ring and coefficient quotients.
- `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` / `Scheme.proEtaleDerivedCategory`;
  its public imports supply the same `Scheme.ProEt.topology`. The coefficient-varying
  categories use the recorded general `ringedSiteModules` and `DerivedCategory`.
- `def-weil-size-convention` has no object or module; universes are explicit.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm` / `integralConstantToCompletion` and
  its public `CompletedIntegralCoefficients` constructions of the actual limit and projections.
- `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` / `SheafOfModules.restrictScalars`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` / `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses` /
  `CategoryTheory.ringedStrictTowerHomotopyLimitOfUniverses`; total-limit models are
  the canonical `Functor.rightDerivedFunctor` with K-injective projection normalization.
- `Sheaf.Paper.NormalizedDVRTower` / `normalizedDVRModules`, `normalizedDVRDerived`,
  `normalizedDVRModuleRes`, `normalizedDVRRes`, `normalizedDVRQuotient`,
  `normalizedDVRRestrictionCompIso`, and the universal Hom normalization of `NormalizedDVRTower`.
- `Sheaf.Paper.IntegralReductionTower` / `integralReductionTower`; its finite-field wrapper
  is imported, while unrestricted tensor reductions use the existing scalar-extension API.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` /
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` /
  `CategoryTheory.derivedInternalHomOfUniverses`.
- `Sheaf.Algebra.Homology.KFlat` / `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift` / `CochainComplex.mapBifunctor`, together
  with its `Functor.map₂HomologicalComplex` total-tensor bifunctor.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` /
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` /
  `CategoryTheory.rhom_global_sectionsOfUniverses`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction` /
  `WeilConjectures.derivedScalarExtensionRestrictionAdjunction` and its actual tensor,
  restriction, universal counit, and ordinary normalized adjunction.

All auxiliary named postponed theorems belong to the construction or characterization
of this node's own site, evaluation, restriction, tensor, Hom, and limit maps; no other
DAG theorem is restated. Their proof docstrings give the relevant componentwise or
universal-property argument. No existing live files or tools were edited.

Additional repair searches: `msearch.py` LeanFinder query "Canonical tensor comparison
on K-flat coefficient-system representatives and degree-zero projection of derived Hom
inverse-limit adjunction" returned eight unrelated Tor/derived-tensor results. Direct
`rg` searches for the new helper names in the upstream and side Lean sources and Mathlib
returned no existing declaration. The ordinary tensor, Hom, localization and homology
infrastructure is reused; only the missing characterizations of this node's maps are added.
Read Stacks `sites-cohomology.tex` at the sequence-site construction/0941,
RHom-well-defined/0A95, internal-hom/08J9, and internal-hom-composition/0A98; the pure
representative formulas are those described by node proof steps 5, 6, 10, 11 and 14.

Repair edge cases: in addition to those above, for chain complexes concentrated in degree
zero over an odd-prime coefficient quotient, a negative scalar tensor comparison violates
its unit/pure-tensor normalization. A corresponding negative closed transpose violates
`uncurry_model`. A negative gamma projection violates the actual H-zero equation on an
identity class. Identity quotients, zero sections, all total degrees, and arbitrary K-flat
representatives occur in the normalizations; no site-universe equality was imposed.

## Historical repair verification

The retained sandbox already contained the H3 repair work. I continued that repair,
retaining the representative normalizations and cycle-normalized Hom equivalences,
and made `CoefficientHomProjection` use the named actual `coefficientGammaZeroMap`.
It applies that map to the inverse integral Hom identification of h, then applies the
finite Hom identification and equates the result with reduction of h followed by
the evaluated counit. Thus this field directly constrains gamma itself.

I repaired a truncated helper-node signature using the shared declaration reader,
regenerated the declaration lists (including the correct closed-structure namespace),
and added the helper module's definition inventory. The node signatures now match
their complete declarations and all lines are at most 100 characters.

The first prescribed wrapper compile found a duplicate declaration in the import
closure of `PbcCompletedPullbackActual` and `PbcActualScalarPullback`, confirmed on
the server. These were proof imports only; I replaced them with the smaller generic
`ModulePullbackPushforwardAdjunction` and
`RingedTopoiCanonicalTensorPullbackOfUniverses` modules, which supply exactly the
ordinary module adjunction and representative-normalized tensor comparison used by
this node's sequence-site proof. No imported library source or dependency record was
changed. The latest main branch is taken by `deliver2.py` itself; no direct git
command or write was made in the shared repository.

Fresh searches through `msearch.py`: LeanFinder query "Canonical normalization of
derived tensor comparisons on K-flat coefficient-system representatives and degree-zero
derived Hom projection of enriched adjunction" returned eight general derived-adjunction
unit/counit declarations, not this coefficient calculus. Mathlib grep query
`coefficientGammaZeroMap|coefficientHomSectionEvaluation|[Ss]ystem.*[Tt]ensor.*[Nn]ormalization`
returned zero hits. The retained LeanSearch, LeanFinder/Loogle and source/DAG searches
above and in `searches.jsonl` cover the constructions and the new definition nodes.


Fresh completion pass (UTC 2026-10-16): the prescribed `scompile.py N0
lem-coef-derived-system-evaluation-calculus` invocation compiled all five delivered
modules separately, including each final library module name, with exit 0 and no
warnings. Final module timings were 27.4 seconds for representative evaluation,
4.3 seconds for the zero-cycle class, 5.1 seconds for the sequence site, 51.9 seconds
for the tensor-Hom model, and 36.4 seconds for the main calculus. Every invocation
retained the 60-second limit; no global build or direct compiler command was used.
The explicit representative tensor result types in the retained repair avoid the
previous final-module export timeout. All five primary node signatures were checked
verbatim against their modules, all Lean lines have at most 100 characters, and the
item differs from the shared base only in `lean` and its four added definition dependencies.

The fresh LeanFinder query "canonical derived tensor Hom representative normalization
and zeroth cohomology of the enriched reduction inverse limit adjunction" returned eight
general enriched-functor projection and ordinary monoidal declarations. None constructs
this coefficient-system calculus or its representative and H-zero normalizations.
Fresh `rg` searches for `coefficientGammaZeroMap`, `coefficientScalarTensorIso`,
`CoefficientTensorModels`, and the item id returned no declaration in the upstream
project, shared side library, or Mathlib. The actual Mathlib
`DerivedCategory.homologyFunctor` and `homologyFunctorFactors` signatures were read in
`DerivedCategory/HomologySequence.lean` and agree with the H-zero transports used here.

The first fresh dry run recompiled all five modules cleanly, then preflight found that
its bracket parser did not recognize the sequence-site node's two combined dependency
citations. I separated them into individual `[lem-pur-derived-change-of-rings]` and
`[lem-weil-derived-scalar-extension-restriction-adjunction]` citations, preserving the
statement and dependency list. Its only other finding was the expected missing
independent second reading. The final prescribed `deliver2.py --no-push` check is rerun
after this metadata repair and these report updates;
its log is retained in `scratchpad/current-repair-dryrun.log`. The worker makes no push
and leaves the independent second reading to the next worker.

## New nodes

`def-coef-hom-representative-evaluation` defines the actual componentwise evaluation
`phi(x)(y)` into the fixed K-injective replacement on an arbitrary ringed site with
independent site and coefficient universes. Its module is
`Sheaf.Paper.CoefficientHomRepresentativeEvaluation`; its five declarations expose the
actual Hom projections, fixed resolution, localization factorization, inverse augmentation,
and section evaluation. These are constructions from Stacks 0A8X, 0A95 and 079P,
extracted from the repaired item to keep both compilations within the 60-second limit.
No comparison is replaced by an arbitrary map and no theorem of another DAG node is
restated. The node uses the existing Hom/resolution declarations without changing them.
LeanSearch and LeanFinder each returned eight general evaluation/injective-resolution
hits; none was this construction. Mathlib grep returned zero hits. Source and DAG searches
found related scheme-only `schemeTensorHomUncurryComponent` and
`def-pc-canonical-derived-tensor-hom-model`, whose Zariski ringed-space interface does
not apply to either the pro-etale site or its ringed sequence site. The blueprint search
for `Hom representative evaluation` returned zero matches. Detailed search outputs are
recorded in the new node's `mathlib_searches`.

The new definition's hypotheses are the arbitrary site `J`, the standard sheafification
instances used by the existing resolution, and the coefficient ring sheaf `A`. Its inputs
are exactly `P,L,M,phi,p,q,k,h,U,x,y`; its output lies in `I(M)^k(U)` and uses the actual
`(q,q+p)` product projection followed by evaluation at the identity of the slice over U.
No K-flat, boundedness or nonzero-section hypothesis is imposed. Zero complexes and
empty-section cases are therefore included. The derived localization and inverse
augmentation helpers use the same resolution instance as the recorded internal Hom.


`def-coef-hom-zero-cycle-class` supplies the missing actual zero-cycle class from the
ordinary section Hom complex to H⁰ of derived global internal Hom. Its module is
`Sheaf.Paper.CoefficientHomZeroClass`. The class is constructed from `homologyπ`,
`homologyFunctorFactors`, the universal right-derived unit and the inverse of the
recorded Hom localization factorization. Its component evaluation uses the fixed
product projection and the identity object of the localized site. Its induced Hom
identification is the recorded RHom/global-sections comparison with a unique
representative normalization, not a second cohomology construction: a cycle representing
f is sent to Q(f) followed by the inverse localized augmentation. Naturality covers
both variables; the representative characterization quantifies over every K-flat source,
every target complex, every cycle and every represented chain map. Source: Stacks 08JA
and 079P. It is independent of the coefficient tower and is needed to type the prescribed
H⁰ gamma identity without choosing an arbitrary natural additive equivalence.

The new node retains arbitrary site object and morphism universes, coefficient/module
universe max(c,v,u), the standard sheafification instances, and an arbitrary displayed
module derived-category localization. Zero complexes, zero cycles, degree-zero identity
cycles and nontrivial negative representatives are all allowed. LeanSearch and LeanFinder
returned only generic complex cycles, Hom cocycles or sheaf-category results; Mathlib
grep, source and side-repository searches found no such canonical sheaf-Hom class.
`blueprint_refs.py search 'Hom zero cycle'` returned zero nodes. The existing
`lem-pur-rhom-global-sections` supplies the abstract natural equivalence but does not
supply this cycle-class map or its representative normalization. All exact search outputs
are recorded in `mathlib_searches` and `searches.jsonl`.

The zero-cycle construction and its generic section helpers were moved unchanged from
the repaired item into this independent definition module to keep the file-only compile
limit. The item still includes every tensor representative equation and directly applies
`coefficientGammaZeroMap` in `CoefficientHomProjection`; this rearrangement changes no
hypothesis, normalization or conclusion.


`def-coef-ringed-sequence-site` names the actual canonical ringed sequence site on
N × W.ProEt, its coefficient ring sheaf, vertical evaluation, exact scalar restriction
to constant-coefficient towers, and total derived inverse limit with its canonical
projections. Its module is `Sheaf.Paper.CoefficientRingedSequenceSite`. All these
declarations were extracted unchanged from the repaired calculus after a full local
compilation passed at 59.8 seconds but the final module-path check timed out at 60.
The final arrangement keeps the same mathematical data and gives each module margin
under that unchanged limit.

The site has object universe t+1 and arrow universe t; module coefficients are in
max(u,t+1). The hypotheses remain a prime l, a finite field extension E of Q_l, and
an arbitrary scheme W, including the empty scheme. The covering predicate is exactly
the vertical-slice condition; its topology proof is postponed as a named theorem.
The actual coefficient ring sheaf, evaluation functor and scalar restriction functor
are fixed on all sections and morphisms, and their existence statements determine
them uniquely. Normalization means precisely invertibility of successive scalar
adjunct transitions. Derived projection maps are fixed on every K-injective tower by
the actual ordinary limit-cone projections. The file also names the recorded finite
derived scalar adjunction and existing internal-Hom/global-section functors; it does
not define alternate versions of these operations. All auxiliary statements retain
their source and complete proof docstrings.

Searches: LeanSearch and LeanFinder for the ringed sequence site of quotient coefficient
sheaves returned general sheaf-module or condensed-module declarations; Mathlib grep
for coefficientSequence/semilinearSystem found no hit. Source/DAG searches found the
record-based `SheafOfModules.CoefficientSystem` for constant quotient rings in
`CoefficientEvaluationDerivedLeftAdjoint`, and the not-yet-recorded
`lem-pur-system-level-left-extension` about such abstract systems and their adjoints.
Neither supplies the ringed sequence site, its coefficient sheaf or its canonical
vertical inclusions. `CompactSupportReductionTower` mentions forming this site only
in its proof docstring. The blueprint search returned zero matches. The new notion
is the canonical site realization needed to use the already recorded general-ringed-site
Hom and K-injective constructions, not another abstract record category or an attempt
to state either of those existing lemmas. Detailed raw results are in the node's
`mathlib_searches` and `searches.jsonl`.


`def-coef-ringed-tensor-hom-model` defines the general ringed-site representative
characterization of a closed tensor-Hom structure, in
`Sheaf.Paper.CoefficientRingedTensorHomModel`. The monoidal data has the recorded
internal Hom as its right adjoint; evaluation/transposition are its counit/Hom
equivalence and composition is the transpose of successive evaluations. Its natural
K-flat comparison is normalized by the actual sheafified total-tensor generators
and the fixed Hom replacement: the uncurried chain map sends x tensor y to phi(x)(y),
and the displayed localized equality identifies it with the very same comparison.
There is no unrelated tensor or Hom choice. Source: Stacks 06YN, 07A4, 08J9 and 0A98.
These generic declarations were extracted unchanged from the repaired calculus; the
coefficient-specific scalar, evaluation and strict-system normalization predicates
remain in the item's module.

The new definition has arbitrary site object/arrow universes, coefficients/modules in
max(c,v,u), the standard sheafification infrastructure and an arbitrary displayed module
derived category. Its normalization quantifies over every K-flat pair, every target
complex, every Hom chain map, all integer degrees, all local objects and all sections.
The total tensor preservation theorem retains its complete source/proof docstring.
Zero complexes, negative degrees, zero sections and every summand are included.
LeanSearch returned generic monoidal closed currying and module tensor evaluation;
LeanFinder returned general complex/condensed monoidal APIs. Mathlib grep found no
counterpart. Source/DAG searches found the existing
`def-pc-canonical-derived-tensor-hom-model`, whose declarations are restricted to
Scheme.Modules on a scheme's Zariski ringed space. It cannot be instantiated at a
pro-etale site or a ringed sequence site. The blueprint search returned zero matches.
The exact searches are recorded in the new node. The definition names a missing
general-site normalization and reuses all actual total-tensor and Hom constructions.

## Earlier second reading (a previous round; superseded)

I am the independent second reader of the retained repair, not its author. I opened
the authoritative node, all five delivered modules, the four new definition nodes,
the recorded dependency interfaces, and the Stacks source. This reading supersedes
neither the node nor its proof plan: the item's mathematical statement is unchanged.
My object/hypothesis/conclusion checklist, in statement order, is as follows.

1. Prime ell, finite extension E/Q_ell, its chosen valuation ring/uniformizer, and
an arbitrary scheme W: the main section binds `l`, `[Fact l.Prime]`, `E : Type u`,
`[Field E]`, `[Algebra Q_[l] E]`, `[FiniteDimensional Q_[l] E]`, and `W : Scheme.{t}`.
The actual coefficient quotient and completion declarations are reused through
`integralCoefficientCommRingSheaf` and `completedIntegralCommRingSheafUnrestricted`.
The chosen uniformizer belongs to the coefficient dependency; no additional
uniformizer or coefficient ring is chosen here. Verdict: exact.
2. Small pro-etale site, strict semilinear systems, componentwise abelian structure:
`coefficientSequenceTopology` on `N x W.ProEt` is exactly the vertical-slice topology;
`coefficientSequenceCommRingPresheaf` uses the actual quotient sequence, and
`coefficientSequenceModules` is its module-sheaf category. The arrows k <= n induce
the required contravariant quotient-linear transitions. Its derived category is
`coefficientSequenceDerived`, the ordinary unbounded localization. Evaluation is
the actual vertical restriction with its coefficient identification, and
`coefficientSequenceEvaluation_exact` supplies componentwise exactness. Verdict: exact.
3. U, total derived limit L, and normalization: `coefficientSequenceRestriction_exists`
fixes both objects and underlying transition/morphism maps, rather than merely
postulating an exact functor. `coefficientSequenceDerivedRestriction` is its exact
localization, and `coefficientSequenceLimit` composes it with the total right-derived
ordinary limit. `coefficientSequenceProjection` uses the actual limit projections
normalized on simultaneous K-injectives. `IsNormalizedCoefficientSequence` quantifies
over every m >= n and every finite target; the specified transition induces a Hom
bijection. The recorded scalar tensor/restriction adjunction makes this precisely
invertibility of the transition adjunct, not invertibility of the restricted map.
Verdict: exact.
4. Functorial reduction on one flat-term K-flat representative, with strict quotient
maps: `reduction`, `reductionEvaluation`, and `reductionModel` in
`CoefficientDerivedSystemReductionModel` give the actual functor and comparisons.
`CoefficientReductionModels` uses one strict complex C and all its comparisons kappa;
the final equations are the actual `coefficientOrdinaryQuotient` transitions.
The latter are fixed by the ordinary scalar adjunction and coefficient quotient.
`coefficientFiniteReductionModel` uses the existing derived-change-of-rings counit.
The flat-term condition occurs only in this representative computation, not as a
restriction on the ambient input P. Verdict: exact.
5. Adjunction, reconstruction unit, counit, and triangles: `adjunction` has type
`reduction` left adjoint to `coefficientSequenceLimit`; hence includes both triangles.
`unit_projection` and `counit_projection` compare with the existing unit-normalized
finite adjunction and the actual total-limit projection. `reduction_normalized`
is asserted for every ambient derived input. There is no reconstruction-isomorphism
condition. Verdict: exact.
6. Simultaneous internal Hom on normalized inputs, fibers, evaluation and
transposition: `coefficientSequenceInternalHom` is the recorded
`derivedInternalHomOfUniverses` on the ringed sequence site. `systemClosed` uses
this very bifunctor as right adjoint. `systemTensorModel` fixes its tensor/transpose
on actual K-flat representatives. `fiberHom`, `fiber_evaluation`, and
`fiber_naturality` impose exactly the finite internal Hom identifications, fixed
by evaluated system evaluation and natural in both inputs. The horizontal
transition identity follows by transposing that system evaluation equation and
cancelling the normalized first-input transition, as in node proof step 10;
it is not inferred from faithfulness of derived evaluations. Verdict: exact.
7. Actual derived tensor and beta, arbitrary P,Q, and all three compatibilities:
`coefficientTotalTensor` is Mathlib's total tensor, and the integral/system/finite
`CoefficientTensorModels` identify its localization with the displayed closed tensor.
`coefficientBaseChangeHom` is reduction of evaluation followed by transposition.
`reduction_compatible` asserts naturality, transposition and internal composition
as system-map equations; `beta_evaluation` is its finite comparison. The scalar,
evaluation and reduction tensor normalizations fix the ordinary pure-tensor
formula and a simultaneous strict chain map before evaluation. No arbitrary-input
beta-isomorphism is asserted. Verdict: exact, including the returned H3 repair.
8. Isomorphism detection: `isIso_iff_evaluations` ranges over arbitrary actual
derived-system morphisms, with all finite evaluations. The reverse implication
is the node's substantive claim; the forward implication is functoriality.
Verdict: exact.
9. Global mapping system H and finite global complexes:
`coefficientSequenceGlobalHom` takes the simultaneous internal Hom, then U, then
total right-derived termwise sections, and lands in D(Tow(Ab)). `globalEvaluation`
and `globalEvaluation_model` use its actual fiber-Hom comparison.
`coefficientIntegralGlobalHom` and `coefficientFiniteGlobalHom` are the existing
internal Hom followed by the total right-derived Hom from the module unit.
These are whole derived complexes, not just their degree-zero groups. Verdict: exact.
10. Specified gamma, arbitrary P and normalized N: `coefficientEnrichedAdjunctionMap`
is the reduction/limit adjunct of beta followed by internal Hom of the counit.
`enriched_isIso` asserts invertibility of this map under precisely those quantifiers.
`CoefficientDerivedSystemCalculus.gamma` is its actual derived-sections image
followed by `globalLimit`. `globalLimit_model` fixes the latter on simultaneous
resolutions using the ordinary sections/limit comparison and universal derived
units. No integral mapping complex is tensored with B_n. Verdict: exact.
11. Actual gamma projections and scalar adjunction: `CoefficientGammaProjection`
starts with `S.gamma.hom`, the actual `coefficientMappingProjection`, and the finite
global-Hom identification. Its other side is postcomposition by the actual
`coefficientSequenceProjection`, the evaluation-defined finite enriched adjunction,
the scalar-section transport, and the reduction identification. The finite
enriched map is invertible; the transport is fixed on sections by b*f(1) and
on resolutions by `scalarSections_model`. Verdict: exact.
12. Degree-zero formula: `CoefficientHomProjection` applies the actual
`coefficientGammaZeroMap` to the inverse integral H-zero Hom identification of h,
then applies the finite Hom identification. Its result is rho_P, reduction of h,
inverse rho_(LN), and the evaluated counit, in that order. The H-zero map is
literally H-zero of gamma followed by its actual projection; the Hom equivalences
are fixed by actual zero-cycle classes and chain maps. Thus the repaired clause
cannot be satisfied by an unrelated scalar-adjunction identity. Verdict: exact.
13. Naturality, composition, units/counits, and simultaneous resolutions:
`CoefficientGammaNaturality` is the two-variable naturality equation.
`CoefficientMappingComposition` is precisely the tensor-parameter equation of
node proof step 15, using the actual counit mate `tensorLimitMap`. Taking the
evaluation parameters specified in that proof yields the mapping-composition
equation; inserting identities uses the already supplied adjunction triangles.
The resolution coherence fields fix the global comparisons before taking fibers.
`coefficientDerivedSystemEvaluationCalculus` existentially supplies this entire
calculus together with its coherence. Verdict: exact.

I checked the dependency signatures rather than relying on their titles. In
particular, `DerivedScalarExtensionRestrictionAdjunction` has independent t and u,
uses the unrestricted completed coefficient sheaf, and supplies the normalized
unit; the older `integralReductionTower` wrapper's finite-field datum is not imposed
on this statement. `NormalizedDVRTower` supplies the same actual finite modules,
quotients and Hom-bijection normalization. `DerivedInternalHomOfUniverses` uses
the fixed functorial K-injective replacement and localization factorization used
by the new helper. `RhomGlobalSectionsOfUniverses` uses the same total sections
and degree-zero Hom interpretation. The total-limit dependency is on strict
module towers, not a choice of limit of objects in a derived category.

I also independently reviewed each new definition node against its source and
module. `def-coef-hom-representative-evaluation` is actual product projection and
local evaluation into the fixed replacement, with the actual localization factor.
`def-coef-hom-zero-cycle-class` constructs its data using homology projection,
the universal derived-sections unit, and that factor; the additive identification
is uniquely fixed by naturality and its represented-chain-map formula.
`def-coef-ringed-sequence-site` is the product site of Stacks' section preceding
0941 with the specified varying ring; its functor choices have object/map or
resolution characterizations and uniqueness. `def-coef-ringed-tensor-hom-model`
is the general-site representative normalization from 06YN/07A4/08J9/0A98:
its generator uses the sheafification unit and actual total summand, and
`uncurry_model` identifies the same comparison with phi(x)(y) into I(M).
None has data-valued sorry or a bare existence choice of unspecified data.
The named postponed theorems state the constructions/properties described by
their owning node and carry source/proof docstrings. All definition nodes have
the required definition fields, searches, ancestry, and direct dependency links
from the item. There are no dependency-module repairs in this packet.

Source reading: `sites-cohomology.tex` at `section-derived-limits` and
`lemma-derived-limit-is-ok` identifies sequence sheaves, exact evaluation and
the simultaneous K-injective total limit. `lemma-K-flat-resolution`,
`lemma-RHom-well-defined`, `lemma-internal-hom`, and `lemma-adjoint`, together
with `injectives.tex` at `theorem-K-injective-embedding-grothendieck`, concern
arbitrary ringed sites/Grothendieck module categories and unbounded complexes.
They impose no geometric finiteness, boundedness, or characteristic condition.
The node explicitly supplies the additional varying-coefficient argument in
its fifteen proof steps; I did not treat Tag 0941 alone as asserting that result.

Edge cases: the fixed positive-exponent tower is indexed by N with exponent n+1,
so Lean n=0 is the first positive quotient and no empty index case was discarded.
The formulas include m=n, zero complexes, zero sections, all integer cochain
degrees, arbitrary unbounded inputs, and the empty scheme. Neither char(W)=ell
nor characteristic zero is excluded. The site has objects in t+1 and arrows in t;
coefficients/modules lie in max(u,t+1), while generic helpers retain independent
c,v,u and the displayed derived-category universe. No additional universe equality
or scheme property is a binder of the final theorem.

Independent searches performed in this pass: LeanFinder query "Derived internal
Hom on a ringed sequence site with quotient coefficients and enriched reduction
inverse limit adjunction" returned light-condensed Hom and general Ext results.
LeanSearch query "The derived internal Hom for normalized inverse sequences over
quotient sheaves of rings has a canonical fiberwise evaluation and enriched
adjunction with total inverse limit" returned ordinary sheaf pullback, evaluation,
and ordinary sheaf Hom results. Loogle `CategoryTheory.Adjunction` returned the
generic adjunction infrastructure already used here. Mathlib grep for
`coefficientSequence|coefficientHomZeroClass|CoefficientTensorModels` returned zero
hits. I also searched upstream WeilConjectures, shared Sheaf and DAG sources for
semilinear systems, sequence sites, tensor-Hom normalizations and zero-cycle classes.
The record-based `SheafOfModules.CoefficientSystem` in
`CoefficientEvaluationDerivedLeftAdjoint` uses constant quotient rings; it is not
the ringed sequence site or this enriched calculus. The scheme-only
`CanonicalDerivedTensorHomModel` does not apply to the pro-etale or sequence site;
ordinary `siteTensorHom` and upstream pro-etale tensor-Hom adjunctions do not supply
this general-site representative normalization or these coefficient-system maps.
No exact existing declaration was found. The fresh search outputs are appended
by the prescribed search wrapper to searches.jsonl.

Mismatches and changes: I found no further mismatch in the retained repaired Lean
or node records. In particular, I checked the previous H3 defects against the
actual pure-tensor/uncurrying equalities and the actual H-zero gamma composite,
not the worker's report alone. I retained all five modules and node signatures
and added this independent clause-by-clause review. I checked that each node's
`lean.statement` occurs verbatim as the complete primary signature in its module,
all lines are at most 100 characters, all variables/universes are explicitly bound,
and all theorem proofs remain sorry. The main theorem docstring follows all
fifteen node proof steps. No statement correction or unit change is required.

Second-reader validation (2026-10-17): the prescribed compile wrapper was run on
all five sibling modules. The subsequent prescribed `deliver2.py --no-push`
completed with exit 0 and `OK (dry run): commit 7ac65e9d4a passes the preflight
and compiles; nothing pushed`. This includes the independent reading above and
the server's fresh-base preflight. The log is
`scratchpad/independent-second-reading-dryrun.log`. Only this validation paragraph
was added after the successful dry run; the five compiled Lean modules and node
signatures are unchanged.

## Historical second reading by N0

The node introduces (1) a prime `l`, finite extension `E / ℚ_[l]`, coefficient
valuation data, and arbitrary scheme `W`; (2) the small pro-etale sequence site,
strict semilinear module systems, componentwise abelian structure, and unbounded
derived categories; (3) termwise restriction `U`, total derived limit `L`, actual
projections, and normalized systems; (4) a functorial reduction computed on one
flat-term K-flat representative with strict quotient maps; (5) its derived
adjunction, unit, counit, triangles, and normalization; (6) simultaneous internal
Hom with actual evaluation/transposition and fiber identifications; (7) the actual
total tensor, beta comparison, and system-level naturality/transpose/composition;
(8) evaluation detection of isomorphisms; (9) the global mapping system and finite
global complexes; (10) the specified enriched gamma isomorphism and its actual
limit comparison; (11) projection and scalar-adjunction formulas; (12) the
degree-zero gamma formula; and (13) naturality, units/counits, composition, and
simultaneous-resolution coherence. The repaired Lean renders these through
`CoefficientDerivedSystemCalculus`, `CoefficientDerivedSystemFibers`,
`CoefficientDerivedSystemResolutionCoherence`, `CoefficientGammaProjection`,
`CoefficientHomProjection`, `CoefficientGammaNaturality`,
`CoefficientMappingComposition`, and the existential theorem
`coefficientDerivedSystemEvaluationCalculus`. Each item matches the node exactly.

The source passages in `sites-cohomology.tex` (the sequence-site construction,
Tags 0941, 06YS, 0A95, and the derived-adjoint discussion) and `injectives.tex`
Tag 079P impose no extra finiteness, boundedness, Noetherian, or characteristic
hypotheses. Searches with LeanSearch, LeanFinder, Loogle, and `rg` over Mathlib,
upstream `WeilConjectures`, shared `lean/Sheaf`, and DAG nodes found no existing
declaration for this varying-coefficient calculus. The four helper definitions in
this delivery are genuine constructions and are cited as new statement
dependencies; no dependency interface required repair.

Edge cases checked: the positive tower is nonempty (Lean index zero is exponent
one), `m = n` transitions are included, zero systems/complexes and zero sections
are allowed, `W` may be empty or have characteristic `l`, arbitrary unbounded
inputs are admitted, and site object/morphism universes remain independent
(`t+1`/`t`, coefficients in `max u (t+1)`). No mismatch was found and no node or
Lean statement was changed in this second reading. The five sibling modules were
compiled with the prescribed `scompile.py` wrapper; the current log is
`scratchpad/second-reader-compile-current.log`.

## Resumed repair verification

The missing H3 transition clause is `CoefficientDerivedSystemFibers.fiber_transition`.
Its actual transition-adjoint, quotient comparison, normalization isomorphisms and
K-flat tensor normalization are described in the opening worker report. The general-site
section and generator helpers change only how these identical formulas are checked.
The focused quotient diagnostic, `scratchpad/abelian-quotient-fixed-profile.log`,
finished in 11.8 seconds and identified one specialized instance argument; the delivered
version uses its existing additive instance. The final required five-module compile and
fresh-base preflight are run by `deliver2.py N0 lem-coef-derived-system-evaluation-calculus
--no-push`, with complete output in `scratchpad/resumed-repair-dryrun.log`. All older
verification and second-reading entries in this report concern historical versions.
The second reader must independently read and deliver this version; this worker does
not push it.

The final dry run's five-module compilation completed cleanly, with the standard
60-second limit per file and no unexpected warnings. This includes the actual library
path of each module as well as the sandbox checks. It then entered its normal worktree
capacity queue for the fresh-main rebase and server preflight; the wrapper's final
verdict is retained in the same `scratchpad/resumed-repair-dryrun.log`. No Lean module
or node record changed after this successful compilation.

## Current worker resumption (2026-10-17)

The retained sandbox already contains the substantive H3 transition repair that was
absent from returned immutable head `24d3ed97d8f8`. I read the actual
`CoefficientDerivedSystemFibers.fiber_transition` equation and its definitions again.
The field identifies the transition-adjoint of the actual sequence-site internal Hom,
under `fiberHom` at m and n, with the finite quotient comparison followed by
RHom(alpha_M inverse, alpha_N), for every normalized M, N and n <= m. The ordinary
unit, derived unit, universal change-of-rings counit and pure-tensor K-flat
normalization determine the quotient comparison. The field's documentation now
names the actual sequence transition and the K-flat characterization explicitly.
No mathematical clause, hypothesis, dependency or primary signature was changed.

Comparison with the current shared main node again found only `lean` and the four
previously authorized new definition dependencies different; source, statement,
proof, proof dependencies, and audit fields agree. The prescribed dry-run wrapper
performs the fresh-main rebase. No direct Git command or shared-library edit was made.

Fresh searches in this resumption: LeanFinder, “Derived internal Hom transitions of
normalized inverse coefficient systems are scalar-extension comparisons transported
by normalization isomorphisms”, returned eight unrelated Dold–Kan, condensed Hom,
Ext, ordinary scalar-extension and representation results. Loogle
`ModuleCat.extendRestrictScalarsAdj` returned six ordinary scalar-adjunction results,
including the actual `1 tensor x` unit formula used here. Mathlib grep
`coefficientSequenceDerivedTransition|coefficientFiniteQuotientHomComparison|fiber_transition`
in CategoryTheory returned zero hits. These searches are recorded by msearch.py.

The edge cases m = n, n = 0 (exponent one), zero systems, empty W, independent
site object/morphism universes, and unbounded complexes remain in the equation.
There is no normalization or invertibility hypothesis on the Hom system itself.
The five-module compile and fresh-base dry-run results for this resumption are
recorded in `scratchpad/resumed-current-worker-compile.log` and
`scratchpad/resumed-current-worker-dryrun.log`. Historical second readings above
remain historical; a new independent second reader must review this repair.

The first fresh compile exposed a current-base import-visibility change: the
sequence-site module could no longer see
`CochainComplex.IsKFlatIndependentCoefficients` and its coefficient-universe
sheafification instances transitively. Its public imports now explicitly include
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, the owning compatibility
module already used by the recorded change-of-rings dependency. This restores the
actual K-flat declaration and the sequence-module abelian instance without adding
an instance, copying a definition, or changing any universe or mathematical statement.

## Final transition-field performance repair (2026-10-17)

The retained repair was re-read against the H3 finding on `24d3ed97d8f8` and
the current shared node. The actual transition-adjoint is the adjunct of
`coefficientSequenceDerivedTransition`; c_(m,n) is the transpose of reduced
evaluation through the recorded derived change-of-rings and its K-flat-normalized
tensor comparison. Both normalization isomorphisms are the actual transition
adjuncts, and the field includes every normalized M, N and n <= m. No hypothesis
on normalization of the internal-Hom system is imposed. The field retains
m = n, first positive level, zero objects, empty W and unbounded inputs.

The first fresh dry run timed out on the calculus module at 60 seconds, after
its sandbox check passed in 47.5 seconds. The prescribed scratch-profile run
passed both checks, including the output-producing check in 51.8 seconds.
To reduce repeated structure-field checking, `CoefficientFiberTransition` now
packages verbatim the full equation, and
`CoefficientDerivedSystemFibers.fiber_transition` asserts this predicate with
its actual tensor data, quotient calculus and fiberHom. This is a definitional
packaging change only; it preserves the primary theorem signature, DAG statement,
normalization constraints and all earlier beta/gamma repairs. The helper has its
source docstring and is recorded in lean.declarations.

Fresh LeanFinder search for derived internal-Hom transitions through quotient
rings returned eight ordinary adic-completion results and no matching statement.
Loogle `ModuleCat.extendRestrictScalarsAdj` returned its six ordinary adjunction
and unit/counit formulas; its unit is the formula used here. Mathlib grep for
`coefficientSequenceDerivedTransition|coefficientFiniteQuotientHomComparison|fiber_transition`
in CategoryTheory returned zero hits. The same helper-name rg search in upstream
WeilConjectures and shared lean/Sheaf returned no hits.

The final prescribed five-module compile and fresh-base dry run are logged in
`scratchpad/final-packaged-transition-compile.log` and
`scratchpad/final-packaged-transition-dryrun.log`. This worker does not deliver.

The final five-module scompile.py run completed with exit 0 and no unexpected
warnings. The calculus sandbox/library checks took 54.9/59.3 seconds, both within
the unchanged 60-second limit. The fresh-base dry run below is the remaining
validation step.

## Scalar-generator compile repair

The next dry run again reached its calculus library check but timed out, after
the sandbox check passed in 56.3 seconds. A further definitional packaging repair
uses the existing general `CoefficientScalarTensorGenerators` predicate also for
`coefficientScalarTensorIso_exists`. The new
`coefficientIntegralScalarUnitSection` is exactly the local section of the
recorded `scalarReductionExtension_adjunction` unit; its body is that unit applied
to x. Expanding this function and the generator predicate gives exactly the
previous quantified pure-tensor equation. The existential remains unique and
quantifies over the same chain isomorphism, P, Q and all degree/local-section
generators. The ordinary evaluation isomorphism, quotient normalization, beta,
gamma and actual Hom-transition equation are unchanged.

The helper has real data, a source docstring and a lean.declarations entry.
The predicate was moved earlier in the same module so no extra module or node
is introduced. Validation for this additional repair is recorded in
`scratchpad/scalar-generators-transition-compile.log` and the final dry-run log.

The named profile also located repeated checking in
`CoefficientDerivedSystemResolutionCoherence.globalLimit_model`: its generated
structure declarations repeated the large exact-localization terms, including a
3.67-second generated congruence computation. `CoefficientGlobalLimitModel` now
contains that equation verbatim, and the field asserts the predicate. It keeps
the same arbitrary complex K, both actual global-limit comparisons, and the exact
restriction localization maps; only the formula's packaging changes. The helper
is recorded in lean.declarations with its source docstring.

The global-limit predicate was checked textually against the original field:
identical after removing whitespace. All five primary signatures remain verbatim
and all Lean lines remain within 100 characters. The final required all-module
compile and fresh-base preflight are performed by the prescribed deliver2.py
--no-push wrapper and recorded in `scratchpad/stable-transition-dryrun.log`.

## Second reading by N0

I independently read the current node statement, its Stacks source place, the
four added definition nodes, and all five delivered Lean modules. The clause
inventory and verdicts are:

1. The fixed data are `l`, `[Fact l.Prime]`, `E` with its field, algebra and
   finite-dimensional hypotheses, and arbitrary `W : Scheme.{t}`. The Lean
   variables and the recorded coefficient extension supply the valuation ring,
   chosen uniformizer, quotients, and completion. Verdict: exact.
2. The small sequence site, its vertical topology, quotient ring sheaf and
   strict semilinear module systems are rendered by `coefficientSequenceTopology`,
   `coefficientSequenceCommRingSheaf`, and `coefficientSequenceModules`; the
   componentwise exactness and unchanged underlying sections are stated. Verdict:
   exact.
3. The ordinary unbounded derived categories, exact evaluations, termwise scalar
   restriction `U`, total derived limit `coefficientSequenceLimit`, and actual
   resolution-normalized projections are present in the sequence-site module.
   Verdict: exact.
4. `CoefficientDerivedSystemReduction` supplies the functorial reduction on one
   flat-term K-flat representative, strict quotient maps, finite evaluation
   identifications, normalized outputs, the derived adjunction, unit/counit
   projections and both triangle data. Verdict: exact.
5. `CoefficientDerivedSystemFibers.quotientCalculus` records the actual finite
   change-of-rings extension, adjunction, counit, ordinary and derived unit
   normalizations, and pure-tensor K-flat comparison. No quotient flatness is
   assumed. Verdict: exact.
6. The closed tensor/Hom structures, actual representative evaluation,
   transposition, composition, and simultaneous tensor normalizations are given
   by `CoefficientTensorModels`, `CoefficientEvaluationCompatible`, and the
   reduction/evaluation tensor predicates. Verdict: exact.
7. `fiberHom`, `fiber_evaluation`, `fiber_naturality`, and
   `fiber_transition` identify the derived internal-Hom fibers and their scalar
   extension transitions using both normalization isomorphisms and the actual
   quotient comparison. Verdict: exact.
8. `isIso_iff_evaluations` states joint detection of system isomorphisms by all
   derived evaluations. Verdict: exact.
9. `coefficientSequenceGlobalHom` and `globalEvaluation` give total derived
   termwise sections and the finite global mapping complexes. Verdict: exact.
10. `CoefficientDerivedSystemCalculus.enriched_isIso` and `.globalLimit` give the
    specified enriched gamma construction and simultaneous total-limit comparison.
    Verdict: exact.
11. `CoefficientGammaProjection` fixes the actual total-limit projection, scalar
    adjunction, section transport, and finite global-Hom identification. Verdict:
    exact.
12. `coefficientGammaZeroMap` and `CoefficientHomProjection` use H-zero of the
    actual gamma composite and state the degree-zero reduction/counit formula in
    the node's order. Verdict: exact.
13. `CoefficientGammaNaturality`, `CoefficientMappingComposition`, and the
    coherence structure state naturality, composition, unit/counit compatibility,
    and simultaneous-resolution normalization. Verdict: exact.

The hypotheses are neither strengthened nor weakened: there is no Noetherian,
boundedness, flatness, characteristic, reconstruction, or arbitrary-input beta
invertibility assumption. Quantifiers retain arbitrary unbounded complexes,
normalized system inputs only where required, and the independent site and
coefficient universes (`t+1`, `t`, and `max u (t+1)`). Edge cases checked are the
first positive level `n = 0`, `m = n`, zero systems and complexes, zero sections,
empty schemes, and characteristic `l`; all remain admitted.

I searched the shared `lean/Sheaf`, upstream `WeilConjectures`, Mathlib-derived
internal-Hom and scalar-adjunction declarations, and the recorded search log for
the sequence-site calculus, representative evaluation, zero-cycle normalization,
and tensor-Hom model. No exact existing declaration was found. The four added
definition nodes are genuine constructions with source and blueprint docstrings;
their interfaces match their node statements and contain no data-valued `sorry`.

No mathematical mismatch was found in this reading. Relative to the shared node,
the sandbox carries the authorized additions of the four statement dependencies
and the complete `lean` declaration record; I retained those additions. The
current repaired transition field and its packaged predicates preserve the node's
full formulas and quantifiers. All five modules compiled cleanly with the required
`scompile.py` wrapper, with no warnings beyond permitted postponed proofs.
