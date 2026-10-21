## Worker report

Item: `lem-per-adic-normalized-fibre-comparisons`, group N0, stage 2.
Main module: `Sheaf.Paper.PerAdicNormalizedFibreComparisons`.
Main declaration: `AlgebraicGeometry.Scheme.AdicFibreComparison.normalizedFibreComparisons`.
All proofs are postponed; definitions have actual data. Existing realization and fibre
packages have explicit definition owners. New comparison and coherence definition modules
package the same clauses without introducing replacement categories or fibre functors.

### Hypotheses and objects

- `k : Type u`, `[Field k]`, `l : ℕ`, `[Fact l.Prime]`, and
  `[Fact (IsUnit (l : k))]` render the field, prime and invertibility assumptions.
- `FiniteTypeBase k` (an abbreviation of the existing
  `WeilConjectures.CondensedERealization.Base k`) is the existing separated finite-type base: its fields are the scheme,
  its `Over (Spec k)` structure, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
  No nonemptiness, connectedness, flatness or condition that g commute with the structure
  maps is added. `base` only repackages its existing geometric consequences for the
  recorded realization API.
- A finite coefficient field is `A : Type u` with `Field A`, `Algebra ℚ_[l] A` and
  `FiniteDimensional ℚ_[l] A`. Finite inclusions are `A →ₐ[ℚ_[l]] B`.
  This permits all the finite intermediate fields of the node, without fixing a redundant
  embedding of each abstract finite field into the algebraic closure. The common-stage
  clauses use the actual `Padic.FiniteCoefficientFields l Ω` and `pbcFiniteField` models.
- `Ω : Type v`, `Field Ω`, `Algebra ℚ_[l] Ω`, `IsAlgClosure ℚ_[l] Ω` is the fixed algebraic
  closure. Its universe remains independent of u.
- `R : ContinuousRational.Family l` is the recorded simultaneous normalized realization,
  whose existence is the realization dependency. The theorem works for every such family;
  this is normalization data, not an extra mathematical condition on the schemes or sheaves.
- The coefficients, integral categories, raw rational categories and scalar functors are
  the published `integralCoefficientSheaf`, `rationalCoefficientSheaf`, `pbcIntegralDatum`,
  `PbcBoundedConstructibleComplete`, `PbcRationalCategory`,
  `pbcRationalScalarExtension`, and `pbcQbarCategory`. The t-structures are literally
  `ContinuousRational.localizedT` and `pbcQbarStandardT`.
- `Fibres` quantifies the recorded `NormalizedFibre.Assertions` at every base and finite
  coefficient field. In particular it retains their intrinsic identification, all adapted
  charts, lattice normalization and fractional-map equations.
- A geometric point is written inline as `κ : Type u`, `Field κ`, `IsAlgClosed κ`, and
  `x : Spec (.of κ) ⟶ X.scheme`. `underlying` uses `SpecToEquivOfField`, as recorded.

### Clause-by-clause rendering

1. Actual completed rational pullback: `heartPull` is the literal full-heart restriction of
   `(R.along E g).raw l E`. It uses the actual completed integral pullback and its
   rationalization through `Along.integral_mem`; it is not an arbitrary t-exact functor.
   The dependency's `pullHeart` supplies only the membership proof. Likewise `heartScalar`
   restricts exactly `pbcRationalScalarExtension`, and `commonHeartPull` restricts exactly
   `pbcQbarCompletedPull`.
2. The first displayed natural isomorphism is `Comparisons.pull`; its endpoint is the
   fibre at `y ≫ g`. The second is `Comparisons.scalar`, with balanced tensor encoded by
   `ModuleCat.extendScalars i.toRingHom`. `AllComparisons` quantifies all finite extensions.
3. The local map prescription is encoded by `UnitNormalization`. `pullModelMap` and
   `scalarModelMap` are actual composites of the recorded J comparison, image of the
   specified presentation and universal derived counit. The existential model isomorphism
   is required to have exactly that morphism as its hom. `presentedFibre` is constructed
   from `Point.intrinsic`, H0 of the presentation and Mathlib's single/H0 isomorphism.
   `germ` uses the actual module-pullback tensor unit and restriction to the final object.
   The pull equation sends a twice-pulled germ back to its original germ. The scalar inverse
   sends `b tensor germ(m)` to `b times germ(1 tensor m)`.
4. `LocalLimits.pull` identifies the actual `c.pull` with localized finite pullback-stalk
   limits. `PullLimit.projection` fixes every finite projection. `IsPullChartMap` fixes the
   intervening chart map by the actual `R.along` comparison, its derived counit, the single/H0
   unit and ordinary pullback-unit germs. `IsPulledLattice` fixes the pulled lattice map on
   every reduction via the canonical etale/pro-etale comparison mate; its rational map sends
   the same integral section to the rationalization of that image. The target presentation
   is required to satisfy `psi.hom = q.hom >> modulePull.map phi.hom >> eta.hom`.
   Thus psi is the pulled presentation of the specified phi. It is not independently chosen.
5. `LocalLimits.scalar` uses `finiteScalarLevel`, the sheafification of
   `(O_B / pi_B^(n+1)) tensor_(O_A) N_n`, restricted to O_B. Using source level n+1
   rather than the minimal ramification-ceiling level gives the identical quotient: the
   transition kills the further source powers, since e >= 1. `finiteScalarUnit` is the actual
   tensor-adjunction unit followed by sheafification. `tau` identifies these levels with the
   target lattice reductions. `IsScalarLattice` requires the integral section map delta to
   commute with the two reduction cones and these finite units; the rational lattice map eta
   is its localization on the same integral sections. `IsScalarChartMap` pins the coefficient
   map pointwise to i and the chart map q to the actual J/T comparison and derived counit.
   The equation `psi.hom = q.hom >> pbcExtend.map phi.hom >> eta.hom` pins the presentation.
   Finally, each component of e sends a quotient of `b tensor w`, whose source projection is
   represented by the germ of m, to b times the target germ of `tau (1 tensor m)`. This is
   precisely the finite stalk-scalar comparison from lem-pod-etale-stalk-tensor-scalar.
   The completion equation fixes a from these e components; the original generating-tensor
   formula identifies the actual inverse of c.scalar after localization. Thus e, a and psi
   all use one finite scalar construction and one lattice identification.
6. `Coherence.pull_id`, `pull_comp`, `scalar_id`, `scalar_comp` and `mixed` state the five
   identity/composition/associator/mixed equations. Their heart comparison maps have the
   recorded raw comparison as underlying morphism. This is possible literally because the
   heart functors are full-subcategory restrictions. Tensor associators are Mathlib's actual
   `extendScalarsComp`, and the unit is `extendScalarsId`. HEq only handles the equal geometric
   composite endpoints or the separately presented but equal underlying functor maps.
7. Chart independence is the universal quantification in `UnitNormalization`, not an
   existence of some convenient chart. For any two local presentations, the derived-counit
   equation fixes their sheaf models, and their fibre maps have the same germ/pure-tensor
   formula. The retained `Fibres.fractions` equations compare fractional lattice changes;
   equal fractions kill their difference after inversion. Common etale refinements compare
   different charts and stratifications. The proof docstring explains the quotient argument.
8. `CommonPoint.functor` is a functor on the actual common standard heart, with finite
   dimensional values, additive and exact. `finite_stage` gives the stated value at every
   finite-stage heart inclusion and is natural on every arrow at that stage. `stageHeart`
   uses the actual pair-category inclusion; only its heart-membership proof is postponed.
9. `CommonAssertions.detects_zero`, `detects_iso`, `detects_zero_map` and
   `detects_short_exact` give the simultaneous detection assertions. Short exactness is an
   iff for each actual short complex; no exactness assumption on it is smuggled in.
10. `Descent.scalar` ties finite-stage normalization to the actual `StageSystem.transIso`
    through the beta comparison. Its auxiliary tensor associator is characterized on every
    pure tensor and supports independent coefficient universes. This specifies the action on
    common-stage morphisms, not just objectwise values. `Descent.pull` identifies the actual
    common pull comparison with scalar extension of finite pull comparisons, using the
    identity underlying raw stage-inclusion/pullback comparison. `identity` and `composition`
    retain the descended equations.
11. `FiniteRanks.lisse` gives a finite locally closed stratification on which the actual
    continuous realization of each finite heart object is lisse. `RankStratification.rank`
    is defined on underlying scheme points; `FiniteRanks.dimension` identifies it with the
    normalized geometric fibre dimension for every geometric lift. `locally_constant` and
    `finite_image` give local constancy on each stratum and finite range.
12. `FiniteRanks.point_independence` is only `Nonempty` of a vector-space iso for two lifts
    of the same underlying point; no canonical path or iso is specified. `support` is the
    nonzero-fibre/rank equivalence. `refinement`, `refines`, `constant_rank`, `positive` and
    `constructible` give the rank-locus refinement and constructible positive-rank locus.
13. `Comparisons.scalar_rank` and `scalar_support` give coefficient-extension invariance.
    `CommonRanks` gives a finite-stage heart representative and the same decomposition,
    dimensions over Ω, lift independence and support for each common heart object.

### Dependency declarations used

The node's recorded declarations and canonical constructions are reused, not copied:

- `Sheaf.Paper.AdicNormalizedFibreExactness`: `NormalizedFibre.Assertions`, `Point`,
  `Heart`, `Lattice`, `ambient`, `realize`, `coefficient` and their recorded normalizations.
- `Sheaf.Paper.ContinuousRationalDerivedRealization`: `Family`, `Along.raw`,
  `Along.comparison`, `Along.counit`, `moduleUnit`, `derivedPull`, `Composition.raw`,
  `Identity.raw`, `FieldChange.comparison` and `Mixed.raw`.
- `Sheaf.Paper.PerAdicCommonStageTruncations`: `perAdicCommonStageTruncations` and the
  `AdicCommonStageTruncations` interface; `pbcQbarStandardT` is unchanged.
- `Sheaf.Paper.PbcQbarCompletedPullback`: `pbcQbarCompletedPull` and `pbcQbarPullFamily`.
- `Sheaf.Paper.PbcScalarExtension`: `pbcRationalScalarExtension`,
  `pbcRationalScalarUnit`, `pbcRationalScalarCompComponent`, finite field inclusions.
- `Sheaf.Paper.PbcQbarCategory`, publicly reexported by `IntrinsicQbarCategory`: the
  actual pair category. No private copy or replacement category is introduced.
- `Sheaf.Paper.AdicCoefficientDatum`, `IntegralUniformCoefficient`, `PbcRationalCategory`,
  `LocalizedTStructure`: the existing completed coefficients, integral origins, raw
  localization and localized standard structure used by the above APIs.
- Mathlib `Scheme.ProEt`, `ProEt.topology`, `SpecToEquivOfField`, `IsAlgClosed`,
  `Topology.IsConstructible`, `Module.finrank`, `ModuleCat.extendScalars`,
  `extendScalarsId`, `extendScalarsComp`, and derived single/H0 comparison.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `FiniteLocallyClosedStratification`; this recorded definition is added to stmt_deps.
- `Sheaf.Paper.CondensedERealization`: its existing separated finite-type `Base` bundle.
  `FiniteTypeBase` is only an abbreviation of it. The old `AdicHeartPullbackFibres` module
  is retired by the route pivot and is not imported. The base-property consequences are
  named helper theorems of the dependency; `stageEmbedding` is the canonical composite of
  the small-model equivalence and the intermediate-field inclusion.
- Proof imports include the recorded lisse-system comparison, inverse-image stalk-germ,
  stalk tensor/scalar theorem, finite adic-limit theorem, common-stage calculus and cones,
  heart short-exact triangles, field scalar exactness, continuous coefficient realization,
  lisse rank decomposition and lisse tensor/scalar extension modules.

The new definition node `def-per-continuous-rational-realization-data` and
the landed `def-per-adic-normalized-fibre-data` own the reused Family and fibre packages. The new realization-data node replaces the added realization existence theorem in stmt_deps.
The original fibre-exactness edge is retained as required by the stage-2 field contract;
the new definition node explicitly owns all of its reused package definitions.
No statement, proof, proof_deps, status or source was changed.

### Edge cases and search record

Checked: empty schemes and empty inverse-image strata; r=0; zero objects and zero maps;
identity g and identity coefficient extension; nonflat g; arbitrarily ramified finite field
extensions; nonconnected lisse strata with varying ranks; distinct algebraically closed
fields over one underlying point; common heart objects only isomorphic to a finite-stage
pair; independent u and v. No affine hypothesis is imposed on a pulled-back chart: one
passes to an affine open neighbourhood of the chosen lift, as the source proof specifies.

Searches before writing (raw launcher output is retained in sandbox searches.jsonl):

- LeanFinder: "normalized geometric fibre functor of constructible adic rational heart
  pullback scalar extension common stage rank loci". Eight hits, led by
  `Scheme.Hom.normalizationDiagram` and scheme pullback tensor constructions; none is the
  requested adic comparison theorem.
- Loogle: "ModuleCat.extendScalars, Module.finrank, CategoryTheory.NatIso". Zero hits;
  tool reports unknown identifier CategoryTheory.NatIso. Mathlib source search supplies
  the `Iso`/functor APIs and tensor associators actually used.
- Mathlib grep through msearch: "normalized.*[Ff]ibre|[Ff]ibre.*[Cc]omparison|finrank.*extendScalars".
  Four unrelated field-theory hits. `rg` in Mathlib ChangeOfRings, homology, limits and
  full-subcategory files identified the primitive constructions used above.
- `rg` in the upstream WeilConjectures source found the canonical etale pullback-stalk
  isomorphism and normalized inverse-image stalk-germ theorem. The exact item identifier
  has no upstream theorem match.
- `rg` in lean/Sheaf found the old `AdicHeartPullbackFibres`, the finite-stage
  `AdicNormalizedFibreExactness`, and a categorical `NormalizedFibreComparisons` module.
  The latter is about pseudofunctor coefficient normalization, not this adic/rank statement;
  the old large theorem does not contain the full new normalized comparison, zero-map and
  rank-locus clauses. None is an exact existing declaration for this node.
- Read the cited BS PDF locally, Section 6.8, and the current node's detailed twelve-step
  proof. The normalization uses its finite-quotient and finite-module arguments.

No STATEMENT-DISPUTED issue and no source-statement correction.

## Dependency modules

`lem-per-adic-stratified-pullback-texact`: its recorded module
`Sheaf.Paper.PerAdicStratifiedPullbackTExact` was initially referenced by the shared record
but was absent from the current published build and then from local sources. Repeated
`scompile.py --source Sheaf.Paper.PerAdicStratifiedPullbackTExact` reports
"Module source unavailable"; a prescribed module-mode import probe likewise failed.
Section 1(B) therefore supplies `Sheaf.Paper.AdicStratifiedPullbackInterface` and changes
only that dependency's lean record. It uses the same actual completed pullback and canonical
continuous coefficient maps. `LocalModels` states concentration on every pulled-back lisse
stratum, `FreeModels` includes the same free rank on every pulled trivializing chart,
and `FreeBalance` pins its ordinary tensor identification on each standard generator,
`PullbackAssertions` states finite/common t-exactness, exact triangulated structures,
normalized all-degree truncation maps, cohomology comparisons, literal heart inclusions and
exactness. `ShiftData` fixes finite shifts via the universal counit and J comparison;
`common_shift_finite` fixes common shifts through actual finite-stage inclusions. Integral
preservation and its reduction witnesses remain the existing `Along.integral_mem` and
actual completed-pullback data inside the recorded Family. Scalar unit/composition/mixed
comparisons remain that Family's actual normalized fields, not new arbitrary maps.

Its source is the unchanged dependency node, BS 6.8.14 and Remark 6.8.15. Its named helper
heart-membership theorems have full source/proof docstrings and are listed in the owning
node's lean.declarations. The empty, rank-zero and nonflat cases remain included.

## Second reading by N0

This worker was started directly by the dispatcher, with an explicit instruction not to
start other agents. No independent reviewer is invented here. The maintainer's independent
delivery review is the required second reading. The worker's own clause audit above checked
the node against the final file, corrected truncation-based heart wrappers to literal
restrictions, added all five coherence equations, retained the actual derived counits,
added explicit common-stage transition compatibility, and kept the algebraic-closure
universe independent using a pure-tensor-normalized associator.

## Validation

All delivered modules compile separately against the live published library through
`scompile.py`, with no errors or warnings other than the expected postponed-proof warning.
The final validation also recompiles after replacing the retired base import.

The initial dry run identified the retired base-module import and a signature-record
extraction error. The delivery now reuses the active realization Base and records signatures
by the final proof delimiter, so named arguments containing `:=` are retained verbatim.

## New nodes

`def-per-continuous-rational-realization-data` owns the already published
`Sheaf.Paper.ContinuousRationalDerivedRealization` definitions, headed by
`AlgebraicGeometry.Scheme.ContinuousRational.Family` (`existing: true`). Its statement
specifies the Base, At, Along, Identity, Composition, FieldChange, FieldComposition, Mixed
and SiteRestriction data, their actual module/derived inverse images, normalized counits,
coefficient maps and coherence equations. It makes no existence assertion. Source:
Bhatt--Scholze 6.8.2, 6.8.11, 6.8.14 and 6.8.15. The recorded definition dependencies are
exactly the notions cited in its statement. The existence theorem stays a proof input.

The previously delivered ownership node `def-per-normalized-fibre-data` is removed.
The current main branch now has `def-per-adic-normalized-fibre-data`, owning all the
same declarations in their new defining module `Sheaf.Paper.AdicNormalizedFibreData`.
Both the item and the comparison-data node cite this landed owner. The exactness theorem
module publicly reexports these definitions. No duplicate is retained.

Searches for both ownership nodes (raw output in searches.jsonl): LeanSearch query
"coherent family of continuous rational derived realizations and normalized geometric fibres
on lattice charts" returned eight unrelated topology/continuous-map declarations; LeanFinder
query "normalized geometric fibre inverse limit etale lattice rational realization family"
returned eight unrelated perfectoid, etale and normalization declarations; Mathlib grep
"ContinuousRational|NormalizedFibre|rationalFiber" returned zero hits. Project grep located
exactly the published packages reused here; upstream WeilConjectures has no such package.
`blueprint_refs.py search` for "normalized fibre" and "continuous rational" returned zero.
The other existing def-a1 section-data nodes take Family as a parameter and do not define it.
No Lean declaration is duplicated, and neither new node depends on this comparison theorem.

`def-per-adic-fibre-comparison-data` owns the finite comparison, common-stage and rank
assertion packages previously in the item module, now in
`Sheaf.Paper.AdicFibreComparisonData`. This additional definition module keeps the same
objects and fields and lets each file compile within the fixed per-file budget. Its named
heart-membership lemmas are exactly the proof obligations needed by its heart functor
definitions. The coherence module imports it; the main item imports the coherence module and adds
the local-limit normalization assertions and the existence theorem. Source: BS 6.8.4, 6.8.14 and 6.8.15. The original item searches and
the new recorded ownership searches found no existing node or equivalent comparison/rank
package; the categorical NormalizedFibreComparisons module concerns a different notion.

`def-per-adic-fibre-coherence-data` owns `AllComparisons`, `Coherence`, `germ`,
`presentedFibre`, the two actual derived-counit model maps, `UnitNormalization` and `Descent`
in `Sheaf.Paper.AdicFibreComparisonCoherence`. These are the unchanged raw-coherence,
germ/pure-tensor normalization and common-stage descent packages. Its source and searches
are as for the comparison-data node. It depends on that core data node and is cited by the
item. The split reduces per-file elaboration without dropping any equation or hypothesis.

## Earlier repair of returned head 33163f20fd3e (superseded in point 2)

1. Added the two existing-definition ownership nodes above, cited directly by the item.
   Removed the previously added realization theorem from stmt_deps: the statement universally
   quantifies `R`, and does not apply its existence theorem. For fibre data, the added
   definition node explicitly owns Assertions, Point, Lattice and their helpers. The original
   fibre-exactness edge is retained: tools/stage2_delivery.py forbids dropping original
   statement dependencies without a source statement correction, and no mathematical
   correction is called for here. No new theorem dependency was added.
2. Replaced standalone `LocalLimits` with `LocalLimits l R ω c` and the explicit normalized
   pullback and scalar equations described in clauses 4 and 5, expressed by the named
   `IsPullLimitNormalized` and `IsScalarLimitNormalized` predicates. All finite projections,
   localization functors, and the scalar reduction cone are retained. The theorem now returns
   this package for precisely the same ω and c as its natural isomorphisms.

The saved packet was dry-run first and passed at 3db837f40cf; the substantive repairs above
were then made to address the independent mathematical review. No live source or launcher
script was edited. The original interface repair is retained; its node copy changes only lean.
The dispatcher explicitly prohibits subagents, so the self-check here does not claim an
independent second reader. The maintainer supplies the independent delivery review.

The scalar localization equation is stated on all generating balanced tensors, avoiding
expensive unfolding of the adjunction-defined scalar associator. This is an equation for
the actual c.scalar component, after Assertions.normalization, with the specified integral
a (itself pinned to scalarCompletionMap); it is not a second unrelated tensor comparison.


First complete repair compilation: scompile.py compiled all four delivered files separately in
dependency order. Published-module timings: interface 36.1 s, comparison data 34.7 s,
coherence data 45.7 s, final theorem module 17.4 s. The separate sandbox-name compilations
also passed, all below 60 s and with only the expected postponed-proof warnings. Splitting
the data modules resolved the timeouts; no timeout limit, launcher script or live file was
changed. The local-limit predicates use explicit coefficient and module universes.

The diagnostic profile found time spent checking autogenerated structure helpers.
The final files suppress those unused generated helpers (genCtorIdx and genSizeOfSpec),
using options already used throughout the project. Coherence, UnitNormalization, Descent
and LocalLimits have only proposition-valued fields and are explicitly Prop-valued; this
retains exactly their equations and removes irrelevant proof-record constructor overhead.
No mathematical hypothesis, equation or chosen comparison changes.

The repaired packet passed server compiler confirmation. Preflight then found two
combined dependency citations in the new normalized-fibre definition node; these now
use separate bracketed node IDs, as required. No Lean statement changed for this fix.


## Repair of returned head 7aee4a4f4eec

The saved packet was inspected and dry-run before any substantive change. The dry run
reported that Assertions had moved out of AdicNormalizedFibreExactness. Current upstream
has the exact definition owner `def-per-adic-normalized-fibre-data`; the packet now reuses
it and removes its obsolete duplicate. The comparison and coherence packages retained from the returned delivery are otherwise unchanged.

Finding 1 remains repaired: the new Family ownership node is retained, and the existing
fibre-data owner is now cited. This adds no theorem-as-definition dependency.

Finding 2 is repaired in substance. The new helper definitions modelH0, finiteUnitMate,
finiteScalarLevel, finiteScalarUnit, IsPulledLattice, IsScalarLattice, IsPullChartMap and
IsScalarChartMap are in the item's own module and listed in lean.declarations. They expose
parts of the very comparison prescribed by the item; no extra existence theorem is assumed.
Their definitions have real data and their proof fields are actual structural proofs.
The sole theorem in the item still has proof sorry.

The pull presentation q uses a source derived model e whose H0 map is the identity and a
target model e' whose hom is exactly pullModelMap. The displayed equality for psi then
uses modulePull(phi) and eta. The reduction-cone equation pins eta to the canonical pulled
system hsystem. Multiplying psi by lambda while leaving that system fixed would require
multiplying the integral cone map by lambda; its fixed projections forbid this in positive
rank. The rank-zero case has just its unique map.

For scalars, the finite isomorphisms tau, integral section map delta, rational lattice map
eta, target presentation psi, stalk-tower map e and completion map a are tied to each other.
Rescaling tau forces the same rescaling of delta, eta, psi, e and a. In the final normalized
formula those changes cancel. It therefore cannot produce lambda times c.scalar, which
was possible when psi and e were independent. Holding the lattice presentation fixed leaves
no such freedom at all. The finite germ formula fixes e on all its generators: each source
finite stalk projection has a germ representative, and tensors generate its scalar quotient.
This check covers arbitrary ramification, identities, rank zero, zero objects, empty charts,
and nonflat g without any new hypothesis.

Source read again: BS PDF pages 58--64, in particular 6.8.4(1),(4),(6), 6.8.6,
6.8.14 and Remark 6.8.15. The latter specifies the actual balanced module inverse image.
The full current node proof steps 2--4 specify the finite germ and scalar-limit construction;
the added constraints implement those steps, including the link to actual T through J.
No source statement correction is needed.

Additional searches for the repair: LeanFinder query "Canonical finite scalar extension of
normalized etale lattice systems and tensor stalk comparison on germs" returned eight
unrelated Tilde, Kaehler-differential and etale-algebra hits. Loogle
"ModuleCat.extendRestrictScalarsAdj, toSheafify" returned zero hits and reported that
its index does not know toSheafify. Mathlib grep
"finiteScalarLevel|finiteScalarUnit|IsPullChartMap|IsScalarLattice" returned zero hits.
Project rg found CompletedLisse.finiteScalarUnit: it requires coefficient rings of Type
(u+1), whereas the specified coefficient fields here are Type u. Its unit/mate formulas
are followed using Mathlib's existing commutative extendScalars adjunction, preserving the
independent scheme and algebraic-closure universes. LisseIntegralSmallCoefficients supplies
the existing small-coefficient Grothendieck instance. No new coefficient universe equality
is imposed. All launcher search output is in searches.jsonl.

Self-check for this repair (the dispatcher forbids a second agent): checked the concrete
lambda-rescaling counterexample above against the final definitions, every finite germ
component and both presentation equations. This is the author's reading, not an independent
review. The Coherence and Descent clauses, detection and rank clauses retain their previous clause
audit; the maintainer provides the independent immutable-head review.

The attempted advisory strengthening of common Descent identity/composition was tested
but made the otherwise accepted coherence module exceed the 60-second limit. That module
has been restored to its returned version; the required H3/H5 repair is entirely in the
item's module. The advisory equations and absence of a separate second worker therefore
remain explicitly advisory. No independent second reading is claimed.

## Final repair validation

The repaired four-file packet passed scompile.py separately in dependency order, both
sandbox and published module-name compilations, with no errors or unexpected warnings.
The new finite scalar constructions also passed their independent module-mode probe.
All 14 declarations of the item's module are recorded in lean.declarations; the module
contains 13 actual definitions and the one postponed main theorem. The main theorem's
signature is still exactly the recorded signature. Static comparison with current main
finds only lean changed for the dependency, and lean plus the permitted added stmt_deps
for the item. Every delivered Lean line is at most 100 characters. The obsolete duplicate
fibre-data owner has been removed in favor of the landed definition node.
