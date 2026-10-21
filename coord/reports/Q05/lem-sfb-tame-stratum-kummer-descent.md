## Worker report

The delivery states `AlgebraicGeometry.ProEtale.CondensedRing.tameStratumKummerDescent`.
It introduces explicit assembly interfaces for the actual augmented root nerve,
ordinary internal derived invariants, their coefficient-unit square and restriction
maps. No mathematical proof is supplied at stage 2. Every postponed theorem has a
source and a natural-language proof in its docstring. The item proof now cites the
corresponding DAG inputs separately in all eight steps. Definitions have real data;
canonical comparisons selected using a theorem are specified uniquely.

The original statement and its original proof are retained. The only item field
added beside `lean` is the list of new definition dependencies. No statement
correction or disputed statement is proposed. The source's all-continuous geometric
input remains the same WANTED input recorded by stage 1; this delivery does not
replace it by a finite-coefficient comparison.

### Hypotheses and clauses

* Distinct primes are `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
  The characteristic field is `(k : Type u) [Field k] [CharP k p]`.
  `PadicAlgCl ℓ` is the existing norm-topological algebraic closure; the finite
  intermediate field is `E : PadicAlgCl.FiniteIntermediateField ℓ`.
* The base scheme and its specified k-structure are `Y : Scheme.{u}` and
  `[Y.Over (Spec (.of k))]`. Finite type is rendered by `LocallyOfFiniteType`
  and `QuasiCompact` for the structural morphism; separation by `IsSeparated`;
  regularity by `_hY : IsRegularScheme Y`. These are actual properties of Y,
  not properties of auxiliary charts.
* `D : Y.IdealSheafData` with `hD : IsStrictNormalCrossingsBoundary D` is the
  existing finite reduced SNC divisor predicate. Its finite component family is
  `kummerComponents D hD`, using the family determined by the SNC witness.
  `I : Finset (Fin hD.2.2.choose)` ranges over every subset of that family.
  `kummerIndices` changes only the universe of the index type. No nonempty,
  irreducible-stratum or positive-rank assumption is imposed.
* `W` is the canonical open `(tameBoundaryOpen D).toScheme`, and the actual open
  immersion is `(tameBoundaryOpen D).ι`. `L : KummerModules ... W` is an internal
  module over the actual all-continuous coefficient ring. `_hL` is
  `IsLisseCoefficientModule ... L`, the existing finite-rank lisse condition.
* `_htame : IsStrictLocalKummerTameModule p ... D ... L` is exactly the existing
  strict-local full prime-to-p compatible-root trivialization condition. It
  includes identity covers when there are no branches. No weaker local-monodromy
  predicate or finite-coefficient condition is substituted.
* `TameStratumKummerAssertion` uses `ParameterStratum C K`, the existing reduced
  exact stratum (intersection of the selected components with all other
  components removed). Its `Scheme.Cover Scheme.proetalePrecoverage` is one
  covering family. The isomorphism `e : B.X α ≅ c.boundary` and equation
  `e.hom ≫ c.boundaryToStratum = B.f α` identify each member over that stratum.
  Both fields use this same covering, chart and representation.
* `TameRootChartGeometry p D c` supplies the actual compatible root characters,
  tower, action, punctured pro-etale cover and torsor comparison. The group
  `kummerChartGroup p K` is exactly the existing `ParameterRootDeckGroup` on
  the selected branch subtype, hence the product of the q-adic integers for
  every prime q different from p. It is not an unspecified profinite group.
* `KummerStratumChart.representation` is the existing finite-dimensional
  continuous `PartialKummer.FiniteRepresentation E.1 G`. Its `primeToEll` field
  says the image of `kummerPrimeToEllInclusion` is finite and its `Nat.card` is
  coprime to ℓ. The inclusion explicitly inserts zero at the ℓ-adic coordinate.
* `KummerCoefficientModels` uses the existing `PartialKummer.Condensation` for
  both fields. Those coordinates identify all profinite sections with continuous
  functions into F tensored with the finite E-vector space. The action is the
  existing condensed action, including all continuous G-valued families.
  `unit_coordinates` fixes every section of the coefficient unit to coordinatewise
  E→Omega inclusion, the finite-basis formula for x↦1⊗x.
* `kummerOmegaModule` is the ordinary module extension of scalars. Its source unit
  is the actual extension/restriction adjunction unit. For E itself the original
  L is used, identified canonically with its identity scalar extension.
* `comparisonE` and `comparisonOmega` have source `kummerOpenImage`, namely exact
  inverse image of the ordinary derived open direct image of L_F in degree zero.
  Their target is `kummerInvariantObject`: ordinary right-derived invariants in
  equivariant condensed modules, canonical localization transport, then exact
  point inverse image. They are isomorphisms of derived module sheaves on the
  entire boundary member. No geometric-stalk or cohomology-object replacement
  appears in the conclusion.
* `KummerGlobalChart.normalization` first uses `kummerLocalizationMap`, the
  actual direct-image counit base-change mate, before the boundary inverse image.
  Thus no erroneous pullback of the open to the boundary is used.
* `KummerResolvedDescent` requires the actual augmented Cech resolution, its
  normalized augmentation and localized quasi-isomorphism, a coherent roof of
  full simplex diagrams, and its finite-diagonal total comparison. The final
  isomorphism is fixed by the displayed composite. The bar resolution retains
  its actual invariant inclusion. This is augmented Kummer-nerve descent, not
  an arbitrarily chosen isomorphism between the final objects.
* `KummerNormalizedChart.nerve_coordinates` uses the canonical successive-root
  vertex map into the actual Cech fibre product in every degree. The coherent
  roof preserves all faces and degeneracies. `column_square` equates each
  resolved column with the actual nerve-coordinate restriction, geometric
  puncture/counit mate, and universal internal-Hom evaluation on the whole
  profinite parameter object. `IsKummerTermComparison` explicitly equates the
  puncture unit followed by the comparison with the pulled-back direct-image
  counit mate. This retains the punctured strict-local counit normalization.
* `KummerInvariantScalarArrow` fixes the right-hand arrow using actual resolution
  lifts of `coefficients.unit`, their augmentation equations, the published
  `scalarInvariantChain`, and its localized normalization equation.
  `KummerStratumChart.scalar_square` compares precisely `kummerSourceScalarMap`
  with this arrow after actual derived restriction of scalars. No flatness of
  the E→Omega coefficient map is assumed or required for this restriction mate.
* `refinementE` and `refinementOmega` now carry, for every scheme S′ and
  g:S′→c.boundary, a full `KummerGlobalChart` with boundary map
  `g ≫ c.boundaryToBase` and root-boundary map `g ≫ boundary`. Its comparison
  is required to equal the original comparison pulled back with
  `kummerDerivedUpperComp`, the associativity transport and
  `kummerInvariantPullbackIso`. The chart carries actual normalized augmented
  descent, so the pullback formula alone cannot inhabit this interface. The
  universal quantifier includes identity maps, composite restrictions and empty S′.
* If I is empty, `empty_tower` requires the actual tower map to be invertible;
  `empty_open` supplies an actual map into W over Y and an actual trivialization
  of the pulled-back L by the same finite model. The Omega model is its ordinary
  scalar extension. This is the requested pro-etale trivialization, rather than
  merely a vacuous group-cohomology assertion.
* The action-category abelian/Grothendieck structures and normalized bar models
  are existential conclusions in `TameStratumKummerAssertion`, not extra
  hypotheses on the input. The larger bar-derived localization is transported
  canonically to the published module-derived universe by `Localization.lift`;
  no equality of site object and morphism universes is imposed.

### Dependency declarations used

* `def-sfb-continuous-map-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`, `Profinite.continuousMapRingSheafOfUniverse`.
* `sk-def-sfb-pulled-back-coefficients`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`, `AlgebraicGeometry.ProEtale.coefficientRing`.
* `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
* `sk-def-sfb-module-derived-pushpull`: `Sheaf.Paper.CondensedModuleDerivedPushpull`, `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPushforward`.
* `sk-def-sfb-dc-setting`: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`, `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`.
* `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
* `def-trf-strict-normal-crossings-boundary`: `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
* `def-sfb-lisse-coefficient-module`: `Sheaf.Paper.CoefficientHeartStratificationDefs`, `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`.
* `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.IsOpenImmersion`.
* `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
* `def-sfb-continuous-map-condensed-ring-map`: `Sheaf.Topology.ContinuousMapCondensedRingMap`, `Profinite.continuousMapRingSheafMapOfUniverse`.

The auxiliary modules reuse `Sheaf.Paper.TameRootTowerExtension` (full root chart,
parameters and geometry, now owned by `def-sfb-tame-root-chart-geometry`),
`Sheaf.Paper.StrictLocalKummerTameModule` (`def-sfb-strict-local-kummer-tame-module`),
`Sheaf.Paper.PartialKummerBoundaryUnitModel` (finite representations and all-continuous
condensations), `Sheaf.CategoryTheory.CondensedEquivariantBarData` (native equivariant
modules, full simplex bar diagrams, invariant models and scalar maps), and the published
ProEtale module-object pullback, pushforward and exact derived functors. The new node
records cite the owning nodes of their imports and the internal-module definitions.

### Edge cases and searches

I checked the empty stratum (empty covering family is permitted), I=∅, an empty
whole divisor, dimension/rank zero, n=0 in the nerve, and arbitrary profinite
parameter objects. The statements impose no hidden nonemptiness or projectivity
of free condensed parameter modules. Finite-dimensional coefficients are expressed
using a rank and basis; rank zero is permitted. H_I has trivial image in the empty
index case and its cardinality is one, which is coprime to ℓ.

The search records in each new node preserve the searches made: LeanSearch for a
normalized coherent Cech/internal-bar full Kummer comparison (eight unrelated
normalization and discrete-cochain hits); LeanFinder for the canonical nerve/bar
counit comparison (eight ordinary bar and Dold–Kan hits); Loogle for Kummer and
Condensed (zero hits); grep/msearch over Mathlib and rg over WeilConjectures and
Sheaf for the helper notions (no matching declaration; an unrelated purity
`kummerScalarMap` was excluded). Blueprint search for Kummer returned 52 existing
nodes, including the full-root, partial-Kummer and bar inputs which are reused.
DAG searches found no node carrying these normalized assembly notions. Ordinary
discrete group cochains and arbitrary derived isomorphisms do not state this input.

## Second reading by Q05

The dispatcher prohibits starting other agents and supplies no second worker. This
is a separate self-audit, not an independent review; the maintainer's independent
reading remains required. I reopened the item and changed modules and compared the
retained packet with the current live source declarations and definition records.

F1: The old restriction record was inhabited for any final isomorphism simply by
pulling it back. It is replaced by actual normalized `KummerGlobalChart` data on
every g:S′→c.boundary for each field. I checked the source over Y is
`(g ≫ c.boundaryToBase) ≫ c.toBase`, the local boundary map is `g ≫ boundary`,
and the equality uses the original chart's comparison after the associativity,
Cartesian-pullback and point-pullback comparisons. Both E and Omega fields use the
same root geometry and their corresponding existing coefficient objects. The
restriction record now preserves the augmented nerve/counit construction.

F2: I removed `KummerParameterEvaluation.lean`, including its duplicated generator,
evaluation, mate, derived map and three postponed laws. The existing:true
`def-sfb-kummer-parameter-evaluation` points directly at the general
`ProfiniteFunctions` definitions. `KummerParameterizedTerm.parameter_iso` uses
`ProfiniteFunctions.comparisonApp` on M[0]. `kummerBarColumnEvaluation` uses the same
map after the canonical evaluation-preserving internal-Hom transport and resolution
presentation. The transport compares the old `Mod.ihom` and the monoidal closed
internal Hom; its existence-and-uniqueness statement fixes the evaluation counit,
so it does not select an arbitrary isomorphism. The C_F specialization remains the
landed `def-sfb-derived-profinite-evaluation`, and invertibility is the existing
`ProfiniteFunctions.comparison_isIso` input, not a new theorem in this packet.

F3: I checked definition ownership by declaration name in the full DAG. Root chart
and geometry constructions now use `def-sfb-tame-root-chart-geometry`; the exact-left
derived adjunction uses `def-sfb-exact-derived-module-adjunction`; point inverse-image
and its composition maps use `def-sfb-condensed-point-pullback-comparisons`; finite
representations and their condensations use
`def-sfb-finite-continuous-kummer-coefficient-model`. Each is an existing:true node
with no new Lean module. The item explicitly cites
`def-sfb-strict-local-kummer-tame-module`. The deleted evaluation module was the only
consumer of `sfbSectionMapOfHom` and `sfbSheafSectionOne`; its theorem-node definition
dependency disappeared with it. Coefficient-section localization remains a legitimate
proof dependency of the item, used in proof step 4. `KummerTermMate` now imports the
actual coefficient-linearization definition module instead of RootTowerCoordinateFace.

F4: The item docstring has eight numbered steps with per-step node ids. Step 1 cites
the extension input; step 2 the prime-to-ell finite-image theorem; step 3 the lisse
and coefficient definitions; step 4 localization and Cech descent; step 5 the full
root-boundary calculation; step 6 the derived invariant bar theorem; step 7 scalar
adjunction and the restriction naturality inputs; step 8 the empty-index extension
case. These match the unchanged DAG proof plan. All recorded proof-input modules are
imported with plain imports unless already present through public statement imports.

I rechecked all original hypothesis/clause correspondences above: distinct primes,
characteristic field, finite intermediate coefficient field, regular separated
finite-type Y, actual finite reduced SNC boundary and exact reduced stratum, lisse
L and strict-local compatible-root tameness, one cover for both fields, the full
prime-to-p group and finite prime-to-ell image, entire derived module-sheaf comparison,
actual scalar unit/square, augmented nerve and counit, every restriction, and the
empty-index trivialization. No item hypothesis or conclusion text was changed.
Empty stratum, I=∅, D empty, rank zero and nerve degree zero remain admitted.
The review's columnwise-roof and empty-index-comparison observations were advisory;
this repair retains the existing coherent-roof and empty-index fields without claiming
those observations were independently resolved.

## New nodes

`def-sfb-condensed-point-pullback-comparisons`: For a commutative condensed ring Lambda and scheme X, derivedFromCondensed is the exact ordinary derived functor of the actual point inverse image on internal Lambda-modules. For f:X→Y, fromCondensedPullbackIso is the canonical module comparison p_Y^* followed by f^* ≅ p_X^*, obtained from upperStarFromPointComp and cancellation of extension/restriction along the same Cartesian coefficient isomorphism. derivedFromCondensedPullbackIso is its canonical image in ordinary unbounded derived categories Built from [sk-def-sfb-pulled-back-coefficients], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Reuses `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity`, `AlgebraicGeometry.ProEtale.CondensedRing.derivedFromCondensedPullbackIso`, with `existing: true`; no module added. The targeted searches and exact definition-ownership scan are recorded in `mathlib_searches`; they found this project construction and no definition node owning the recorded interface.

`def-sfb-exact-derived-module-adjunction`: For a commutative condensed ring Lambda and any scheme morphism j:V→T, take the recorded total derived adjunction Lj^* ⊣ Rj_*. Define punctureDerivedAdjunction by transport of its left adjoint along the canonical isomorphism from left-derived inverse image to exact termwise inverse image. Thus its actual unit and counit are those of the recorded derived adjunction under that fixed comparison; it assumes no puncture-invariance theorem Built from [def-sfb-module-derived-pushpull-adjunction], [sk-def-sfb-module-derived-pushpull], [sk-def-sfb-module-objects]. Source: direct-image proof paragraph (3). Reuses `Sheaf.Paper.RootTowerPunctureInvariance`, `AlgebraicGeometry.ProEtale.CondensedRing.punctureDerivedAdjunction`, with `existing: true`; no module added. The targeted searches and exact definition-ownership scan are recorded in `mathlib_searches`; they found this project construction and no definition node owning the recorded interface.

`def-sfb-finite-continuous-kummer-coefficient-model`: For a normed field E and a topological group G, PartialKummer.FiniteRepresentation is a finite-dimensional E-representation with its finite-basis coordinate continuity. Its action is the norm-continuous action on all continuous G-valued parameter families. PartialKummer.Condensation over a normed field F with a specified ring homomorphism E→F records the equivariant condensed internal module together with the sectionwise identification with continuous functions P→F^d for every profinite P, including its scalar and action formulas. This is the finite-basis realization of C(P,F tensor_E M), with rank zero permitted Built from [def-sfb-continuous-map-condensed-ring], [def-sfb-profinite-coefficient-linearization], [def-sfb-condensed-equivariant-bar-data], [sk-def-sfb-module-objects]. Source: direct-image proof paragraph (3). Reuses `Sheaf.Paper.PartialKummerBoundaryUnitModel`, `AlgebraicGeometry.ProEtale.PartialKummer.Condensation`, with `existing: true`; no module added. The targeted searches and exact definition-ownership scan are recorded in `mathlib_searches`; they found this project construction and no definition node owning the recorded interface.

`def-sfb-kummer-bar-resolution`: On the existing equivariant internal bar model, define its explicit full simplex diagram and exact point pullback of its nonnegative resolution. Transport the bar derived localization to the published small module-derived localization by its universal property. Resolved bar data includes the actual forgotten injective resolution, all normalized internal-Hom term components, and the finite-total comparison normalized on every coprojection. The resulting column map is universal parameter evaluation, and the total comparison uses the existing normalized invariant augmentation. Built from [def-sfb-kummer-resolution-columns], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Uses [def-sfb-kummer-parameter-evaluation]. Uses [def-sfb-condensed-point-pullback-comparisons]. Uses [def-sfb-profinite-coefficient-linearization]. The two existing internal-Hom presentations are identified by the unique natural isomorphism whose actual evaluation counits agree after the canonical tensor quotient and braiding. Its existence and uniqueness, included here as the presentation law, determine this transport; the derived column map then composes its ordinary derived image with ProfiniteFunctions.comparisonApp. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerBarResolution`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-cech-descent`: For Cartesian internal coefficients, define sections over a scheme over W by upper-star followed by lower-star, and restriction by the actual adjunction unit. Apply this contravariant functor to the actual augmented Cech nerve of v:T→W, then to a:W→Y and exact s:S→Y inverse image. This defines the coherent cosimplicial image, its nonnegative resolution, its ordinary derived limit and its unit augmentation. The restriction maps satisfy identity and composition, are additive, and cosimplicial module diagrams are Grothendieck abelian. Built from [sk-def-sfb-module-derived-pushpull], [lem-weil-pbc-right-adjoint-preserves-kinjective], [lem-pc-derived-category-locally-small], [sk-def-sfb-module-objects]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerCechDescent`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-chart-geometry-maps`: For the published full-root chart, use the actual two projections of its local open pullback. Their composites with the punctured root-cover map agree with the actual tower map and the actual original-open map. These equalities retain the localization before boundary pullback. Built from [def-sfb-kummer-constant-nerve-term], [def-sfb-kummer-parameterized-term], [def-sfb-kummer-stratum-geometry], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerChartGeometryMaps`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-coefficient-models`: Bundle the given all-continuous coefficient ring objects and their actual continuous inclusion as commutative ring objects. Both coefficient modules are the existing all-continuous condensations of one finite-dimensional continuous E-representation. Their equivariant scalar unit is normalized on every profinite section by coordinatewise inclusion E→Omega, the finite-basis form of x↦1⊗x. Built from [def-sfb-kummer-scalar-restriction], [def-sfb-kummer-stratum-geometry], [def-sfb-kummer-bar-resolution], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerCoefficientModels`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-coherent-roof`: A coherent roof between a resolved Cech diagram and the resolved existing internal bar diagram is one nonnegative complex of full simplex diagrams with two chain maps, column quasi-isomorphisms and invertible localized finite-total maps. Its derived total comparison is normalized by composing the two actual localized total arrows. Every face and degeneracy is preserved before localization. Built from [def-sfb-kummer-bar-resolution], [def-sfb-kummer-geometric-columns], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerCoherentRoof`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-constant-nerve-term`: Given an actual punctured identification v*L≅p_V*M, the constant-nerve comparison is the unique composite of the canonical root-coordinate pullback compositions, equality of structural maps, the pulled-back supplied identification, and the point-pullback comparison. Its hom component is specified explicitly. Exact derived point pullback of a degree-zero module and the parameterized structural-map equation are included. Built from [def-sfb-kummer-nerve-transport], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerConstantNerveTerm`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-geometric-columns`: The actual n-th Cech projection followed by a is the structural map of a nerve term. Its resolved column is identified with the resolved direct image by the unique chain isomorphism whose components are the published direct-image composition maps. The column map uses the actual derived unit. A normalized geometric term is a derived isomorphism satisfying the inverse-puncture-unit and actual-counit-mate equation. Built from [def-sfb-kummer-resolution-columns], [def-sfb-kummer-term-mate], [def-sfb-kummer-nerve-coordinates], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerGeometricColumns`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-global-chart`: The global chart comparison starts from the actual entire-boundary restriction of the original open direct image. It is required to equal the actual counit-normalized localization map followed by the normalized local root-nerve comparison, and that localization map is invertible. The local open is formed before the boundary pullback. Built from [def-sfb-kummer-normalized-chart], [def-sfb-kummer-invariant-scalar-map], [def-sfb-kummer-local-source], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerGlobalChart`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-invariant-scalar-map`: Define the right-hand derived object as exact point pullback, after canonical localization transport, of ordinary right-derived invariants of the existing all-continuous equivariant module. Define its actual invariant-resolution complex and resolution comparison using the actual augmentation. The point scalar comparison is the canonical module inverse-image comparison. Built from [def-sfb-kummer-coefficient-models], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerInvariantScalarMap`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-local-source`: Define the entire-scheme restriction s*Ra*L[0] in the ordinary internal module-derived category. Localize the open by pulling it back to a chart before restricting to the boundary. The localization map is the actual base-change mate of the open direct-image counit, followed by the exact boundary pullback and degree-zero coefficient comparison. Built from [def-sfb-kummer-nerve-transport], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerLocalSource`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-nerve-coordinates`: For a continuous commutative profinite action over a quotient, define vertex i by multiplying the first lift by the first i group coordinates. The actual wide-pullback universal property defines the map V[G^n]→Cech(v)_n. Its structural map is the parameter projection followed by v. These are scheme maps on whole profinite parameter objects, including n=0. Built from [def-sfb-tame-root-chart-geometry], [def-sfb-kummer-cech-descent], [def-sfb-condensed-equivariant-bar-data], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerNerveCoordinates`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-nerve-geometric-map`: Given the actual punctured constant-module identification, derive its pullback along the canonical root-coordinate map using the exact degree-zero and point-pullback comparisons. Restrict the actual derived nerve image along that map by its actual unit, transport the identical structural maps, and follow the normalized full-root parameterized geometric map. This is a morphism of derived module sheaves on the entire boundary scheme. Built from [def-sfb-kummer-constant-nerve-term], [def-sfb-kummer-parameterized-term], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerNerveGeometricMap`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-nerve-transport`: Define equality transport for actual derived direct images, and restriction along a specified map θ by the actual adjunction unit and direct-image composition comparison. Apply a supplied coefficient identification only after that map. Degree-zero pullback, derived pullback composition and equality comparisons are the published exact Cartesian comparisons. Built from [def-sfb-kummer-geometric-columns], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerNerveTransport`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-normalized-chart`: A normalized chart is a resolved coherent Cech-to-bar descent with the actual punctured constant-module identification and invertible canonical root-coordinate maps. For every n, the column square equates the actual resolved Cech image followed by root-coordinate restriction and geometric counit mate with the actual bar-column universal internal-Hom evaluation. Thus the comparison preserves all continuous parameter families, faces, degeneracies and invariant augmentation. Built from [def-sfb-kummer-resolved-descent], [def-sfb-kummer-nerve-geometric-map], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerNormalizedChart`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-parameter-evaluation`: For a commutative condensed ring R, scheme X and profinite P, use the existing free internal module R[P]. Define its universal parameter generator, tensor/internal-Hom evaluation after point pullback, and its ordinary derived evaluation. The comparison p_X^* RHom(R[P],N) → R(rho_P)_*p_{X[P]}^*N is precisely the rho_P-adjunct of that derived evaluation, using the canonical point-pullback comparison. Its natural transformation is natural in N. These are the existing ProfiniteFunctions constructions, also specialized to all-continuous coefficients by def-sfb-derived-profinite-evaluation; no invertibility assertion is part of the definition Built from [def-sfb-condensed-free-module-adjunction], [def-sfb-profinite-test-objects], [sk-def-sfb-pulled-back-coefficients], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull], [def-sfb-derived-profinite-evaluation]. Source: direct-image proof paragraph (3). Reuses `Sheaf.Paper.ProfiniteConstantDerivedFunctions`, `AlgebraicGeometry.ProEtale.ProfiniteFunctions.comparisonApp`, with `existing: true`; no module added. The targeted searches and exact definition-ownership scan are recorded in `mathlib_searches`; they found this project construction and no definition node owning the recorded interface.

`def-sfb-kummer-parameterized-term`: For j:V→T, q:T→U, i:S→T and i q=s, form the actual parameterized square on every profinite P. A parameterized term retains the normalized full-root geometric isomorphism and asserts invertibility of the existing ProfiniteFunctions.comparisonApp on M[0]. Its geometric map is the actual geometric counit mate followed by the canonical boundary point-pullback identification. Built from [def-sfb-kummer-nerve-transport], [def-sfb-kummer-parameter-evaluation], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerParameterizedTerm`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-refinement`: For an actual normalized global Kummer chart on S, a refinement-natural family assigns to every scheme morphism g:S′→S an actual KummerGlobalChart over g composed with the boundary-to-base map, with the same root geometry and coefficient object. Its comparison equals the exact Cartesian pullback of the original comparison, including the associativity transport and canonical point-pullback comparison. Thus each restriction retains the augmented nerve and actual counit normalization, for identities and composites as well. Built from [def-sfb-kummer-invariant-scalar-map], [def-sfb-kummer-local-source], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull], [def-sfb-kummer-global-chart]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerRefinement`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-resolution-columns`: Define the n-th column of a complex of full simplex diagrams by evaluation. Alternating cofaces, flip, and finite-diagonal total give the actual signed total functor on such complexes. The canonical resolved image-column map uses the actual right-derived direct-image unit and the inverse exact pullback of the supplied resolution augmentation. Built from [def-sfb-normalized-kummer-comparison], [def-sfb-kummer-parameter-evaluation], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerResolutionColumns`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-resolved-descent`: A resolved descent consists of actual injective resolutions, normalized Cech augmentation, its invertible localization, one coherent Cech-to-bar roof, normalized resolved bar data, and a derived-object comparison. Its hom is required to equal the composite of the actual resolution comparison, the augmented finite total, the coherent roof comparison and the normalized bar-invariant comparison. Both finite-total presentations use one definition, so their identification is the identity on every coprojection. Built from [def-sfb-kummer-coherent-roof], [def-sfb-kummer-local-source], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerResolvedDescent`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-scalar-invariant-square`: The scalar-invariant resolution map is the published scalarInvariantChain after the canonical exact point scalar comparison. A derived scalar arrow is normalized by actual lifts of the insertion-of-one map and of the restricted injective resolution, their augmentation equations, and a commuting localized invariant-resolution square. Its vertical scalar chain map is a quasi-isomorphism. This fixes the induced ordinary-derived-invariant coefficient map after scalar restriction. Built from [def-sfb-kummer-invariant-scalar-map], [def-sfb-kummer-local-source], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerScalarInvariantSquare`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-scalar-restriction`: For the actual all-continuous E→Omega coefficient map, define exact derived restriction and ordinary tensor extension. The unit is x↦1⊗x. The derived direct-image restriction comparison is the right-adjoint mate of the normalized scalar/pullback isomorphism, without a flatness hypothesis. The source coefficient map is the image of that ordinary unit followed by this mate and the exact scalar/pullback comparison. Built from [def-sfb-all-continuous-scalar-mate], [def-sfb-kummer-term-mate], [def-sfb-coefficient-map], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerScalarRestriction`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-stratum-chart`: For the exact published full parameter-root deck group, a simultaneous stratum chart consists of one root geometry with compatible characters, the boundary map killing every root, one finite continuous E-representation with finite prime-to-ell image, its two all-continuous coefficient models, both normalized global derived comparisons, their actual invariant scalar arrow and coefficient square, and their exact refinement formulas. For empty I the tower is invertible and the E-module has an actual pro-etale pullback trivialization; the same coefficient model supplies Omega. Built from [def-sfb-kummer-global-chart], [def-sfb-kummer-scalar-invariant-square], [def-sfb-kummer-chart-geometry-maps], [def-sfb-kummer-refinement], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerStratumChart`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-stratum-geometry`: Lift the given finite SNC component family and a chosen finite subset only to the site universe, preserving the actual components and subset. Define H=(product over q≠p,ell of Z_q)^I and its inclusion in the existing full parameter-root deck group by inserting zero in ell coordinates. Finite prime-to-ell image means the representation image of this subgroup is finite and its order is coprime to ell, including rank zero and empty I. Built from [def-sfb-tame-root-chart-geometry], [def-sfb-finite-continuous-kummer-coefficient-model], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerStratumGeometry`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-kummer-term-mate`: For a commuting square i q = π s, define the base-change map as the adjunct of the pulled-back actual direct-image counit. Define the direct-image composition comparison by conjugate adjunctions. The full-to-punctured map is direct image of the actual open adjunction unit; a normalized punctured-term isomorphism composes with that very map to the base-change mate. Built from [def-sfb-normalized-kummer-comparison], [def-sfb-profinite-coefficient-linearization], [def-sfb-condensed-point-pullback-comparisons], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerTermMate`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-normalized-kummer-comparison`: Define the alternating Cech cochain functor, its Cech-first nonnegative bicomplex and finite-diagonal signed total. A normalized augmentation has component in resolution degree q equal to the actual covering unit inserted into Cech degree zero. The injective-resolution comparison is the actual right-derived unit comparison followed by exact inverse image. All simplex operators are retained. Built from [def-sfb-kummer-cech-descent], [def-sfb-condensed-equivariant-bar-data], [def-sfb-exact-derived-module-adjunction], [def-sp-double-complex-total], [thm-sp-double-complex-spectral-sequences], [sk-def-sfb-module-objects], [sk-def-sfb-module-derived-pushpull]. Source: direct-image proof paragraph (3). Module: `Sheaf.Paper.KummerNormalizedComparison`. The retained LeanSearch, LeanFinder/Loogle, and grep searches found no exact normalized assembly interface; its dependency records now cite definition owners of the constructions used.

`def-sfb-tame-root-chart-geometry`: For a finite SNC component family C on Y and I a finite subset, a TameRootExtensionChart is an affine etale chart of the exact stratum open, with branch parameters and an affine weakly etale refinement U. Define its actual full parameter-root tower, boundary base change, punctured tower and punctured base, and their canonical maps. For a prime p and boundary D, TameRootChartGeometry consists of compatible root characters, the full deck-group action rotating the actual roots, its restriction to the punctured tower, the actual pro-etale covering and the invertible torsor comparison (x,g) ↦ (x,gx), all over their specified bases Built from [def-sfb-full-parameter-root-tower], [def-sfb-profinite-coefficient-linearization], [def-trf-strict-normal-crossings-boundary], [def-sfb-strict-local-kummer-tame-module], [def-weil-pbc-proetale-site]. Source: direct-image proof paragraph (3). Reuses `Sheaf.Paper.TameRootTowerExtension`, `AlgebraicGeometry.ProEtale.TameRootChartGeometry`, with `existing: true`; no module added. The targeted searches and exact definition-ownership scan are recorded in `mathlib_searches`; they found this project construction and no definition node owning the recorded interface.

### Postponed theorem inventory

* `KummerCechDescent`: `overSectionsMap_laws`, `cechImage_additive`, `cosimplicialGrothendieck`. All have `sorry` and complete source/proof docstrings.
* `KummerNormalizedComparison`: `kummerAlternating_additive`, `kummerCochains_additive`, `kummerCochains_term`. All have `sorry` and complete source/proof docstrings.
* `KummerNerveCoordinates`: `kummerNerveVertex_over`, `kummerNerveCoordinateMap_over`. All have `sorry` and complete source/proof docstrings.
* `KummerGeometricColumns`: `kummerCechColumn_term`, `kummerCechColumnComposition_existsUnique`. All have `sorry` and complete source/proof docstrings.
* `KummerBarResolution`: `kummerExplicitBar_additive`, `kummerInternalHomComparison_existsUnique`. All have `sorry` and complete source/proof docstrings.
* `KummerParameterizedTerm`: `kummerParameterSquare`. All have `sorry` and complete source/proof docstrings.
* `KummerConstantNerveTerm`: `kummerSquareModuleIso_existsUnique`, `kummerSquareDerivedModuleIso_existsUnique`, `kummerPuncturedParameter_over`. All have `sorry` and complete source/proof docstrings.
* `KummerChartGeometryMaps`: `kummerChartOpen_commutes`, `kummerChartToOpen_commutes`. All have `sorry` and complete source/proof docstrings.
* `KummerNerveGeometricMap`: `kummerNerveMap_toBase`. All have `sorry` and complete source/proof docstrings.
* `TameStratumKummerDescent`: `tameStratumKummerDescent`. All have `sorry` and complete source/proof docstrings.

Coordinate data retains equality to the actual root-coordinate lift, not just an unspecified nerve isomorphism. Its over-base equality is carried explicitly to avoid repeated elaboration of its construction. The derived square helper is chosen only from an existence-and-uniqueness statement specifying its actual canonical composite.

The final coefficient model carries `closureForRing` and `closureForRing_eq`, so the bundled action has exactly the existing condensation data. Its unit coordinate normalization is evaluated after that equality transport. `KummerCoefficientSquare` is the explicit equation using the actual `kummerSourceScalarMap` and exact derived restriction; the stratum chart instantiates it with its two actual comparison isomorphisms.


### Repair searches and validation

The retained packet first passed `deliver2.py --no-push` as f484bbf0c79; that was
only the baseline mechanical check, and the numbered mathematical returns were
then repaired. No direct git command or read-clone edit was used.

New targeted searches: LeanSearch for canonical universal profinite-parameter
evaluation returned eight general sheaf pullback adjunctions; LeanSearch for affine
Kummer chart geometry returned eight general etale/Kummer field constructions;
LeanFinder for exact condensed point pullback returned eight condensed/free-module
and general category interfaces; LeanFinder for the finite-dimensional continuous
representation model returned finite-basis continuity and discrete condensed free
modules; Loogle for Profinite and ihom returned zero; msearch grep for the exact
published names returned zero Mathlib hits. Exact query strings, result lists and
digests are in the new existing:true nodes. `rg` across Mathlib and WeilConjectures
found no matching constructions; `rg` in Sheaf located the exact published modules
listed above. Definition-node declaration scans found no owners of these interfaces.
Blueprint searches for Kummer chart and derived condensed pullback returned zero;
search for derived adjunction found the existing general adjunction node, which
`def-sfb-exact-derived-module-adjunction` now cites for its exact-left normalization.

The obsolete evaluation module and its three postponed theorem declarations are
absent. Its remaining resolution-presentation helper belongs to the bar node, together
with the canonical evaluation-preserving internal-Hom transport and
`kummerHomResolutionEvaluation`, which presents the published evaluation map on
the resolved source. None redefines the universal evaluation arrow.
All compiles use scompile.py, each delivered module separately in dependency order,
with the published server library and default limit. The complete 25-module
scompile run passed with exit code 0. The repaired delivery dry run passed preflight
and all per-file compiles as commit 61a114f392c. A final dry run checks this report
and the explicit per-step proof imports before delivery.
