## Worker report

This delivery states `AlgebraicGeometry.Etale.isIso_finiteCompactProjection` in
`lean/Sheaf/AlgebraicGeometry/FiniteCompactProjectionFormula.lean`. Its proof is `sorry`.
The three coefficient instances have real data: the recorded finite-ring theorem,
the bottom (discrete) topology, and its defining discreteness proof. They introduce
no replacement coefficient ring, tensor, pullback, compact-support functor, comparison,
or origin-witness notion. There are no new definition nodes. The second reading repairs one existing dependency
record, as described below; no additional dependency module is delivered.

Hypothesis and clause correspondence:

- The fixed finite-field datum is `D : WeilConjectures.FiniteFieldDatum.{u}`.
- The prime is `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`. The extension is
  `E : Type (u + 1)`, `[Field E]`, `[Algebra (Padic l) E]`, and
  `[FiniteDimensional (Padic l) E]`. The actual coefficient ring throughout is
  `Padic.coefficientExtensionRing l E n`. The positive level is `n : ℕ` with
  `[Fact (1 ≤ n)]`; `finiteCompactProjectionCoefficient_finite` supplies its finiteness
  from `Padic.finite_coefficientExtensionRing`, rather than adding a hypothesis.
- `X,Y : Scheme.{u}` are k-schemes by their `Over (Spec (CommRingCat.of D.k))`
  instances. Each structure morphism has `LocallyOfFiniteType` and `QuasiCompact`.
  These are the recorded definition of finite type. There is no separatedness
  assumption on either structure morphism.
- `f : X ⟶ Y`, `[f.IsOver (Spec (CommRingCat.of D.k))]` is a k-morphism.
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]` express exactly
  separated finite type.
- `c : Compactification f` specifies an arbitrary computation of compact support.
  This is a universal choice of the data used to define the map, not an additional
  restriction on f: compactifiability follows from the stated geometric hypotheses.
  The proof node explicitly proves invertibility for every such c, without assuming
  equality of transformations from mere independence of their functors.
- `K,L : DerivedCategoryModule ... X/Y` are the ordinary constant-coefficient small
  etale derived objects. `_hK,_hL : DerivedCategory.isBoundedConstructible ...`
  impose precisely the recorded constructibility of every cohomology sheaf and
  vanishing outside a finite interval. The source's other constructibility predicate
  is not substituted.
- `_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn ... Y a b L` is exactly
  finite Tor amplitude tested against every module sheaf in degree zero. Empty
  intervals are permitted by the recorded definition; enlarging one if needed gives
  an ordered interval. No Tor hypothesis is imposed on K.
- The first conjunct is `IsIso (((projectionMapOfCompactification ... c).app K).app L)`.
  Its source is `Rf_! K ⊗ᴸ L`, its target `Rf_!(K ⊗ᴸ Lf* L)` by the two upstream
  bifunctor definitions. The upstream definition is exactly the counit-defined proper
  projection followed by inverse open-extension tensor comparison and pullback
  composition. The compact-support comparisons are imported unchanged.
- Naturality in K and L is built into the natural transformation of bifunctors used
  literally in the conclusion. It applies to every ambient derived morphism, with no
  restriction on a morphism preserving a chosen bound or witness.
- The second conjunct quantifies over arbitrary `Kp,Lp` in the recorded finite
  coefficient pro-etale D-plus categories and `wx,wy : Scheme.EtaleOriginWitness`.
  These are the retained pairs, with their specified comparison isomorphisms alpha.
  `_hx : wx.L.obj ≅ K`, `_hy : wy.L.obj ≅ L` identify their representatives with
  the inputs satisfying the displayed hypotheses. This includes every admissible
  witness, since one can choose K and L to be exactly those representatives.
- The pro-etale map is literally `ProEtale.projectionMapOfCompactification`, the
  third component of `finiteExchangeProjection` in the recorded `ExchangeProjection`
  dependency. Its inputs are the canonical inverse realization of `Kp.obj,Lp.obj`:
  `(finiteCoefficientRealization ...).mapDerivedCategory.asEquivalence.inverse.obj`.
  This transports the ringed coefficient presentation to the fixed-ring presentation
  of that map, without selecting an arbitrary map or forgetting the witnesses.
  Exact termwise comparison is the recorded `siteComparisonDerivedPullbackPlus`;
  compatibility with realization is used in the proof's witness transport. Naturality
  is again that of the actual pro-etale natural transformation.

Dependency declarations read and reused (module: declaration):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`. Additional recorded declarations: `WeilConjectures.FiniteFieldDatum`, `WeilConjectures.FiniteFieldDatum.extensionSubfield`, `WeilConjectures.FiniteFieldDatum.extensionEmbedding`, `WeilConjectures.FiniteFieldDatum.geometricFiber`, `WeilConjectures.FiniteFieldDatum.extensionPoints`, `WeilConjectures.FiniteFieldDatum.pointCount`, `WeilConjectures.FiniteFieldDatum.CoefficientDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`. Additional recorded declarations: `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`. Additional recorded declarations: `AlgebraicGeometry.IsProper`, `AlgebraicGeometry.IsSeparated`, `AlgebraicGeometry.UniversallyClosed`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`. Additional recorded declarations: `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory`, `DerivedCategory.Plus`, `DerivedCategory.Bounded`, `DerivedCategory.homologyFunctor`, `AlgebraicGeometry.Etale.DerivedCategory.torsionCohomology`, `CategoryTheory.Sheaf.IsTorsion`.
- `def-weil-pbc-constructible-complexes`: `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`. Additional recorded declarations: `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`, `AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory`.
- `def-kun-tor-amplitude`: `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`, `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`. Additional recorded declarations: `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`, `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeGE`.
- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`, `AlgebraicGeometry.Etale.derivedTensor`.
- `prop-weil-pbc-inverse-image-modules-exact`: `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`, `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `def-amb-etale-compact-support`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactification`.
- `lem-amb-etale-compact-comparisons`: `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`, `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`. Additional recorded declarations: `AlgebraicGeometry.Etale.etaleCompactSupport_refinementComparison_eq`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_id`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso_comp`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_hom_eq`, `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlusCompIso_assoc`.
- `def-kun-projection-formula-map`: `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`, `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`. Additional recorded declarations: `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_app_app`, `AlgebraicGeometry.Etale.homEquiv_symm_rightDerivedLowerStarProjectionMap`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjection`, `AlgebraicGeometry.ProEtale.coefficientExtensionExchangeProjection`. Additional recorded declarations: `AlgebraicGeometry.ProEtale.finiteExchangeProjection`, `AlgebraicGeometry.ProEtale.coefficientExtensionExchangeProjection`, `CategoryTheory.compactificationExchangeFromData`, `CategoryTheory.compactificationProjectionFromData`, `CategoryTheory.ExchangeProjectionStage`, `CategoryTheory.ExchangeProjectionStage.exchange`, `CategoryTheory.ExchangeProjectionStage.compactExchange`, `CategoryTheory.ExchangeProjectionStage.projection`, `CategoryTheory.exchangeProjectionCoefficientRepresentative`, `CategoryTheory.ExchangeProjectionComparisonPreserves`, `CategoryTheory.ExchangeProjectionAdjunctionComparison`, `CategoryTheory.ExchangeProjectionScalarCocycle`.
- `def-weil-pbc-etale-origin-witness`: `Sheaf.Paper.RingedEtaleOriginWitness`, `AlgebraicGeometry.Scheme.EtaleOriginWitness`. Additional recorded declarations: `AlgebraicGeometry.Scheme.etaleOriginRing`, `AlgebraicGeometry.Scheme.etaleOriginScalars`, `AlgebraicGeometry.Scheme.etaleOriginScalars_locallyBijective`, `AlgebraicGeometry.Scheme.etaleOriginScalars_isLocallyInjective`, `AlgebraicGeometry.Scheme.etaleOriginScalars_isLocallySurjective`, `AlgebraicGeometry.Scheme.etaleOriginRealization`, `AlgebraicGeometry.Scheme.etaleOriginRealization_properties`, `AlgebraicGeometry.Scheme.etaleOriginRealization_additive`, `AlgebraicGeometry.Scheme.etaleOriginRealization_preservesFiniteLimits`, `AlgebraicGeometry.Scheme.etaleOriginRealization_preservesFiniteColimits`, `AlgebraicGeometry.Scheme.etaleOriginComparison`, `AlgebraicGeometry.Scheme.EtaleOriginWitness`, `AlgebraicGeometry.Scheme.finiteOriginFunctionRing`, `AlgebraicGeometry.Scheme.finiteOriginConstantComparison_isIso`, `AlgebraicGeometry.Scheme.finiteOriginConstantIso`, `AlgebraicGeometry.Scheme.finiteOriginToConstant`, `AlgebraicGeometry.Scheme.FiniteEtaleOriginWitness`.
- `def-sf-comparison-derived-pullback`: `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`, `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`. Additional recorded declarations: `AlgebraicGeometry.ProEtale.siteComparisonDerivedPullbackPlus`.

The signatures and docstrings were read from the recorded local side modules or
slopmaster2 sources. The pro-etale projection and flat-pullback instances were read
from the side `lean/WeilConjectures` sources. A compiler probe checked the full
origin-witness, realization, derived comparison and both projection-map signatures
against the current server library. All recorded proof modules with a usable module
record are imported non-publicly; no other DAG node is stated here.

Edge cases checked before drafting:

- Empty X or Y: there is no nonemptiness binder, no choice of a geometric point in
  the statement, and every available compactification is allowed.
- Zero K or L: the constructibility, boundedness and Tor predicates permit zero;
  empty Tor intervals do not exclude it. No nonzero hypothesis occurs.
- Level n = 1 is included. Level zero is excluded exactly by the source's positive
  coefficient level. The distinct-prime hypothesis remains explicit.
- Identity morphisms and identity witness isomorphisms are retained; the arbitrary
  witness quantifiers also include noncanonical representative isomorphisms.
- Arbitrary finite-type k-schemes are allowed; separatedness is required only of f.
  A finite Tor bound on K is not smuggled in through a ctf input category.
- The site universe is u, the coefficient and module universe u+1, exactly as in
  the recorded derived categories; no equality of different site universes is added.

Searches performed:

- `msearch.py ... leanfinder "finite coefficient compact support derived projection formula
  for bounded constructible etale complexes finite Tor amplitude"`: eight unrelated
  affine-limit, Nobeling and derived-fraction results; no matching statement.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.projectionMapOfCompactification"`:
  Loogle does not know that project identifier; this is not evidence of absence.
- `msearch.py ... grep "isIso.*projectionMap|finite.compact.projection" AlgebraicGeometry`:
  zero Mathlib hits.
- `msearch.py ... leansearch "compactly supported etale derived projection formula finite
  coefficients"`: eight support/topology/etale-ring results, no matching statement.
- `rg` in Mathlib, upstream WeilConjectures, and side lean/Sheaf for projection-map and
  node-id names located the existing canonical maps, the stronger etale-only
  `Etale.isIso_projectionMap_of_finite`, and
  `Etale.isIso_projectionMap_coefficientExtensionRing` belonging to `thm-sf-pf-finite`.
  None states this node: the first does not include the witnessed pro-etale assertion;
  the latter adds separatedness of the schemes over k and likewise lacks that assertion.
  The canonical maps themselves are reused rather than defined a second time.

There is no statement dispute or statement correction. The previous attempt's stale
claim conclusion was checked against the current files: the NK report is a stage-1
split report, and the local item has no Lean record. A new statement is therefore
needed; no previously landed statement is intentionally re-recorded.

## Second reading by N1

The source node is the finite-coefficient compact-support projection formula in
`main-20261015/sec-six-functors-basics/sk-thm-sf-pf-finite`, with the master copy
having the same statement. I checked the source proof and the recorded dependency
signatures before checking the Lean signature. The Stacks sources read were
`sites-cohomology.tex`, equation-projection-formula-map (0B56),
lemma-projection-formula (0944), and remark-compatible-with-diagram (0E48), and
`etale-cohomology.tex`, proposition-describe-jshriek (03S5). They add no separatedness
over the field or finite-Tor condition on `K`. The first source constructs the
counit-defined map for arbitrary ringed topoi; 0944 supplies the perfect-input
argument; 03S5 supplies extension-by-zero stalks and exactness.

Object and hypothesis checklist:

1. `D : FiniteFieldDatum.{u}` is the fixed finite-field datum; the Lean declaration
   uses exactly `WeilConjectures.FiniteFieldDatum` and its base field `D.k`.
2. `l`, `Fact l.Prime`, `_hl : l ≠ D.p`, `E : Type (u+1)` with field, Padic-algebra,
   finite-dimensional hypotheses, and `n` with `Fact (1 ≤ n)` are the recorded
   positive finite coefficient convention. The three local coefficient instances
   expose finiteness and discreteness without adding a mathematical hypothesis.
3. `X,Y : Scheme.{u}` have `Over (Spec (CommRingCat.of D.k))`, locally finite type,
   and quasi-compact structure maps. No separatedness of either scheme is added.
4. `f : X ⟶ Y` is over the base, separated, locally finite type, and quasi-compact,
   exactly the separated finite-type morphism in the node.
5. `c : Compactification f` is universally chosen, so the assertion applies to
   every specified compactification.
6. `K` and `L` are the recorded `DerivedCategoryModule` objects over
   `Padic.coefficientExtensionRing l E n`; `_hK` and `_hL` are precisely bounded
   constructibility. `_hTor` is the tensor-vanishing finite Tor-amplitude predicate
   for `L` on `Y`; no Tor condition is imposed on `K`.
7. The first conclusion is `IsIso` of the actual etale
   `projectionMapOfCompactification` component at `K,L`, hence retains its
   counit/open-comparison construction and naturality in both arguments.
8. The second conclusion universally quantifies the finite-coefficient pro-etale
   `Kp,Lp`, their `Scheme.EtaleOriginWitness` data, and the supplied isomorphisms
   from the etale representatives to `K,L`; it asserts `IsIso` of the actual
   `ProEtale.projectionMapOfCompactification` component on the canonical inverse
   realization objects. This is the node's witnessed pro-etale clause, with no
   arbitrary map or existence-only witness substituted.

Edge cases checked: empty schemes and empty fibres have no hidden nonemptiness
hypothesis; zero coefficient modules and zero complexes are admitted; identity
morphisms and identity witness isomorphisms are included; `n = 1` is included while
`n = 0` and `l = D.p` are excluded by the stated coefficient assumptions; no finite
Tor bound on `K`, no separatedness over the field, and no equality of site and module
universes is imposed. The site universe is `u` and coefficient/module universe is
`u+1`, matching all dependency declarations.

Independent searches in this reading:

- LeanFinder, `compactly supported direct image tensor projection isomorphism finite
  Tor dimension constructible complexes`: eight condensed-module and complex-tensor
  results, no matching statement.
- LeanSearch, `Derived tensor projection formula for direct image with compact support
  on constructible etale sheaves`: eight scheme-pullback, tensor, and sheaf results,
  no matching statement.
- Loogle, `IsIso, tensor`: unknown identifier `IsIso`; this is not absence evidence.
- Mathlib grep, `projection.*compact|compact.*projection` under AlgebraicGeometry:
  zero hits. Independent `rg` of upstream and side sources found the etale-only
  `isIso_projectionMap_of_finite`, the downstream coefficient theorem with extra
  separatedness on X/Y and no pro-etale clause, and the pro-etale theorem requiring
  finite Tor amplitude on both inputs. I opened those signatures: none states this
  whole node. The canonical maps are reused.

Mismatches repaired in this reading:

- The statement module had omitted the recorded proof-dependency modules. I added
  their non-public imports, retaining public imports for statement dependencies.
- `lem-cbc-extension-zero-projection-formula` recorded a parallel finite-coefficient
  split module, which collides with the standard operations at
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarComp`. I read the standard upstream
  owning module and rebound the record to
  `WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriekProjection`.
  Its actual `derivedOpenImmersionLowerShriekProjectionIso` is the same unit/tensor
  adjunction map, and its inverse has the displayed projection direction. The item
  now cites this already landed dependency; no replacement construction is defined.
- The historical `def-weil-pbc-proetale-modules` repair is already superseded by the
  current live source. I fetched that source through `scompile.py --source`, removed
  the stale dependency module and node copy from this delivery, and removed its
  redundant item dependency. They are preserved only as scratch history.

The owned theorem required no statement change. Its signature is verbatim the node's
`lean.statement`, all variables/universes are bound, lines are at most 100 characters,
and its only proof is `sorry`. The complete final module compiles cleanly with
`NT_SCOMPILE_LOCAL=1 scompile.py` in both sandbox and library positions (5.4 and 6.3
seconds); see `scratchpad/second-reader-canonical-open-compile.log`. This authorized
local wrapper resolves the stale-live server overlay encountered on the default route.
The superseded failure history is preserved in scratchpad/second-reader-report-with-history.md.
It is omitted from the review packet because it does not describe this delivery.

## Dependency modules

`lem-cbc-extension-zero-projection-formula` is repaired under section 1(B) by an exact
existing-declaration record, with no new module. The former split module imports a
parallel `leftDerivedUpperStarComp` and cannot coexist with this item's canonical
standard operations. The replacement owning module already defines the same
`derivedOpenImmersionLowerShriekProjectionIso` and its invertibility instance; its
inverse is exactly the node's map `(j_! K) tensor L -> j_!(K tensor j^* L)` on arbitrary
unbounded complexes. Finiteness, zero objects and empty opens remain included. Its
statement and every non-Lean node field are unchanged.

## Reviewer fix (maintainer review)

The non-public proof-dependency import `Sheaf.Paper.FiniteCoefficientFlatModel`
(the recorded module of `lem-sf-flat-model`) is removed. Since side commit
4b050b8948 ("Restore public imports pruned in live") that landed module publicly imports
both `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` (live) and
`Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` (side), which declare the same
names, so it no longer compiles on the server (`environment already contains
AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf._proof_2`), and every importer
fails with it. The statement does not use that module; stage 3 restores the import once the
landed module is repaired. No declaration, signature or docstring changes.
