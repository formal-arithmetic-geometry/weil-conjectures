## Worker report

Repair of returned immutable head f133502b9519 (H3/H4, H8/H11). The initial
required dry run of the saved packet passed mechanically (d34f0b0c62), but the
mathematical self-check confirmed the returned defect. The saved stage record
allowed arbitrary categories, operations and a zero projection, so its theorem
was false. That record and its assertions have been removed. This delivery uses
current main's stage-1 statement and five-step proof, with only the permitted
Lean record and additional landed statement dependencies changed.

The module is `Sheaf.Paper.SfProEtaleProjectionFormula`, with primary declaration
`WeilConjectures.sf_proetale_projection_formula`. It states the four clauses as a
conjunction. Its only postponed proofs are the main assertion and
`SfProEtaleProjection.integralDomains`, the typing/completion facts implicit in
writing its integral arrow. Both have source references, blueprint markers and
complete natural-language proof plans. Definitions contain real data.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The standing setting is `D : FiniteFieldDatum`, `l`, `[Fact l.Prime]`,
  `hl : l ≠ D.p`, and the actual finite extension E of `Padic l`, quantified
  separately in each clause. Independent `v` permits a larger algebraic closure.
* The k-schemes are `X.Over (Spec (.of D.k))` and the corresponding Y instance.
  Finite type means `LocallyOfFiniteType` and `QuasiCompact` for each structure
  map. The same two instances for f, `f.IsOver`, and `IsSeparated f` render the
  separated finite-type k-morphism. Structural separatedness of X or Y is not
  added, nor is a properness assumption on f.
* `c : Compactification f` is arbitrary. Its `i`, `g`, `Z`, and `comm` give
  exactly the chosen open/proper factorization, so every clause holds for every c.
* Finite coefficients are `Padic.coefficientExtensionRing l E (n+1)`; n ranges
  over all naturals, so this is every positive exponent and excludes no allowed
  level. K and L belong to the intrinsic constant-ring derived categories.
  `_hK` and `_hL` use the recorded `finiteTorConstructible`, which includes bounded
  constructibility and finite Tor amplitude, on the respective schemes.
  `_wK`, `_wL` retain `FixedEtaleOriginWitness` with the bounded-constructible
  predicate on its actual etale complex, and an isomorphism from the existing
  intrinsic realization of its fixed-scalar target. This is the helper `Origin`:
  it packages the recorded witness and existing coefficient equivalence, and
  introduces no alternative etale-origin notion or comparison functor.
* The finite arrow is the existing `finiteRingCompactSupportProjection` evaluated
  on K,L, not a supplied morphism. Its definition transports the canonical
  proper-counit/open-extension projection to intrinsic constant-ring modules.
  The finite clause explicitly supplies proofs hS,hT that the two endpoints are
  bounded below for the canonical derived t-structure, and asserts `IsIso` of
  `ObjectProperty.homMk P.hom` in `DerivedCategory.Plus` of intrinsic constant-ring
  modules. Its full faithful equivalence to the fixed-scalar presentation gives
  exactly the node's D+ assertion; no endpoint bound is left implicit.
* Integral K,L are literally `sfIntegralConstructibleCategory l E X/Y`, over
  `completedIntegralCommRingSheafUnrestricted`, not a discrete constant O_E.
  `_hK`, `_hL` are the recorded `finiteTorConstructibleIntegral`, including the
  common Tor interval for every reduction. `_wK`, `_wL` retain etale-origin
  witnesses for every positive finite reduction.
* The integral arrow `integralMap` has endpoints in that actual constructible
  complete category. `completedSource` is the quotient-Roos completion of
  `(Rf! K) tensor L`; `completedTarget` is Rf! of the quotient-Roos completion of
  `K tensor f*L`. Completed tensor absorbs completion of the pullback factor,
  giving the same completed tensor with completed pullback. All ordinary tensors
  have the existing `ProEtaleTensorModel` signed K-flat representative comparison.
  These are tensor presentations, not arbitrary operations or projection maps.
* More explicitly, with eta the recorded `IntegralOnSlice.completionUnit`, its
  underlying arrow is
  `inv(eta_source) ≫ PurCompactSupport.projectionMap.app K.app L ≫ Rf!.map eta_inner`.
  The existing `PurCompactSupport.projectionMap` is the canonical proper counit
  followed by its normalized inverse open projection and pullback composition.
  Thus `eta_source ≫ integralMap.hom = ordinaryPF ≫ Rf!.map eta_inner`. This is
  the completed projection's unit normalization, not the choice of an isomorphism
  between endpoints. `integralDomains` states source-unit invertibility and the
  constructible complete membership of both completed endpoints. These facts
  concern exactly this construction, and have no projection-formula-isomorphism
  assumption. The second clause asserts `IsIso` of this explicit completed arrow.
* The rational clause applies the existing
  `sfRationalConstructibleLocalization.map` to `integralMap`, for EVERY integral
  constructible representative. Raw localization has precisely these objects.
  There is no added finite-Tor, chosen-lattice, or origin hypothesis at this stage;
  the residue-Tor theorem supplies the integral domain automatically.
* The algebraically closed clause uses every finite coefficient field F in Ω,
  the existing small coefficient model `Coefficient.{u} l Ω F`, the actual raw
  localization map, and `GeneralAlgebraicallyClosedCoefficients.inclusion F`.
  Consequently its `IsIso` is in the recorded literal-pair category with colimit
  Hom groups. Each pair is represented at its own finite stage; any pair of input
  stages admits a compositum. Quantifying every F and all its representatives
  therefore covers every common-stage representative, including two inputs
  initially at different fields. No idempotent completion is used.

Dependency declarations used (public modules and exact names):

* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` and
  `Sheaf.Paper.FiniteFieldFiber`: the standing coefficients and `FiniteFieldDatum`.
* `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`,
  `finiteTorConstructibleIntegral`; the field clause is the recorded unrestricted
  constructible category, as in `finiteTorFieldCoefficientCategory`.
* `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`.
* `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
* `Sheaf.Paper.FiniteRingCompactSupportProjection`:
  `AlgebraicGeometry.Scheme.finiteRingCompactSupportProjection`; its public
  intrinsic module equivalence is `sfIntrinsicModuleEquivalence`.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
* `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `WeilConjectures.PurCompactSupport.completed`, `image`, `pull`, `projectionMap`,
  `completedPull_comp`. These helpers apply to the full geometric scope here;
  this delivery does not apply that file's stronger geometric theorem binders.
  Its public `ProEtaleTensorModel` comes from
  `Sheaf.Paper.ProEtaleCanonicalTensorPullback`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationProjectionFromData`,
  used inside that existing canonical `projectionMap`; neither its operations
  nor its comparison data are arbitrary parameters in the new theorem.
* `Sheaf.Paper.IntegralDerivedOperationsOnSlices`:
  `WeilConjectures.IntegralOnSlice.completion`, `completionUnit`, using the
  original small pro-etale site (object universe u+1, morphism universe u).
* `Sheaf.Paper.SfRationalizationKaroubi`:
  `WeilConjectures.sfRationalConstructibleLocalization`.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.inclusion` and its
  literal-pair category; `AlgebraicallyClosedCoefficients.Coefficient`.
* `Sheaf.Paper.SfIntegralCompactSupportConstructible`:
  `sfCompactSupportCoefficientFinite`, the positive-quotient finiteness instance.

The five additional statement dependencies are existing landed nodes owning these
canonical finite/integral projection constructions, integral operations, bounded
constructibility, and positive finite-coefficient interface. No new DAG node or
replacement dependency module is needed. The auxiliary typing statement and
transport package belong to this node and are listed in `lean.declarations`.

Edge cases checked: zero inputs and empty schemes give the canonical zero-object
maps, not arbitrary endomorphisms; identity and proper compactifications use the
same unit/counit composite; n=0 denotes the allowed residue quotient of exponent 1;
all higher positive exponents are included; ramified E and the identity coefficient
extension are allowed; non-separated X/Y are allowed when f is separated; different
initial finite fields for two algebraically closed inputs are covered after their
compositum; the algebraic closure universe is independent. At no stage can one
replace the projection by an unconstrained zero map. There is no disputed node
statement or statement correction.

Searches made during this repair:

* msearch.py leanfinder: "canonical compact support projection formula on completed
  integral pro etale constructible derived categories and scalar localization".
  Eight hits: BDeRhamPlus, BDeRham, Condensed.profiniteSolidCounit,
  Condensed.profiniteSolid, Condensed.profiniteSolidification,
  Condensed.instIsRightKanExtensionFintypeCatCondensedModProfiniteProfiniteSolidProfiniteSolidCounit,
  Condensed.profiniteFree, AlgebraicGeometry.exists_appTop_map_eq_zero_of_isLimit.
  Read types: none states this projection formula.
* msearch.py loogle: `"projection", "IsIso"`: zero hits.
* msearch.py grep: `projectionFormula|projectionMap|ProjectionFormula|lowerShriek`,
  Mathlib/CategoryTheory: zero hits.
* rg on the older upstream WeilConjectures tree for this node id found the legacy
  ProjectionFormula, ScalarExtension and LowerStarProjectionComparison modules.
  Read their coefficient signatures: their discrete integral coefficient model
  does not give the completed/raw/common-stage statement here.
* rg on the current Sheaf tree for `projectionMap`, `projectionMapOfCompactification`,
  and completed-tensor comparisons found FiniteRingCompactSupportProjection and
  IntegralCompactSupportCoefficientComparison. Their full canonical definitions
  were read and reused, rather than replaced. The 51-module condensed framework
  was also checked against coord/pefw-upstream-framework.md; its coefficient
  categories do not substitute for this node's completed/raw/common categories.

## Second reading by Q49

This is a separate self-review, not a claim of an independent second worker.
The dispatch explicitly prohibits starting other agents. I reread the current
node statement, its source unit, all seven original dependency interfaces,
additional canonical-map interfaces, and the repaired file side by side.

The earlier report's claim that the supplied projection was canonical was false:
no such constraint occurred in its type. The repaired file has no arbitrary
category, functor or projection-map binder. Every coefficient category and each
map now comes from the named recorded construction, with completed-unit
normalization made explicit. The earlier claim about absence of finite-Tor
conditions was also inaccurate: both finite and integral conditions are now
literal binders, and finite-level witnesses are retained. Field inputs are all
objects of raw localization, so no lattice restriction is smuggled in. Tensor
model binders carry the signed K-flat representative comparison and cannot be
used to inject an unrelated operation or projection map.

Both theorem docstrings now include source, blueprint marker, full hypotheses,
and a proof plan explaining all stages and their canonical maps. The separate
integral typing statement's proof plan explains residue invertibility, uniform
Tor bounds, constructibility, completion units and the absence of structural
separatedness assumptions. The old unsupported second-reading assertions have
been replaced by this explicit audit.

Validation: the prescribed `scompile.py Q49 sk-thm-sf-pf-proetale
lean/Sheaf/Paper/SfProEtaleProjectionFormula.lean` completed with exit 0 for the
final file, both sandbox and library checks. There were no errors or unexpected
warnings. The JSON primary signature was checked verbatim against the file;
all nine declarations are listed, and no old generic stage record remains.
