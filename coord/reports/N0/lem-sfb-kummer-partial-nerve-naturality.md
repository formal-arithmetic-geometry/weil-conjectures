## Worker report

This is a stage-2 statement of `lem-sfb-kummer-partial-nerve-naturality`, not a
stage-1 re-split. The live node is split and its stage-1 review is PASS; those
fields and its mathematical statement are preserved. The theorem proof is the
single expected `sorry`. Its docstring gives the fourteen-step natural-language
proof, with the named DAG inputs. All helper definitions contain actual data or
specifications of the conclusion, never a choice from a postponed existence
statement.

Module: `Sheaf.Paper.KummerPartialNerveNaturality`.
Namespace: `AlgebraicGeometry.ProEtale.KummerPartialNerve`.
Main declaration: `kummer_partial_nerve_naturality`.

The source is the node's main-20261015 direct-images proof, paragraph (3), and the
agent-expanded successive-root argument recorded in this node. The source and
node explicitly say that an exact all-continuous geometric reference is WANTED;
this delivery does not claim that this missing reference has been supplied.

Hypotheses, in their order in the node:

- Distinct primes: `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
- Characteristic-p field: `(k : Type u) [Field k] [CharP k p]`.
- Norm-topological algebraic closure and finite intermediate field:
  `PadicAlgCl ℓ` and `(E : PadicAlgCl.FiniteIntermediateField ℓ)`, with their
  already supplied normed-field structures. No discrete topology is substituted.
- All continuous coefficient functions: `fieldRing` is an abbreviation for the
  published `CondensedRing.kummerCoefficientRing`, whose underlying sheaf is
  `Profinite.continuousMapRingObj F`. It does not build a second ring structure.
- Coefficients on a scheme and internal modules: `PartialKummer.SchemeModules`
  is precisely `Mod` over `condensedRingObj`; all geometric functors are the
  published `CondensedRing.upperStar` and `moduleObjectDerivedPushforward`.
- Regular separated finite-type k-scheme: `Y`, its structure morphism `y`,
  `[LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]`, and `IsRegularScheme Y`.
  The first two finiteness instances together express finite type.
- Reduced finite SNC boundary: `D : Y.IdealSheafData` and
  `hD : IsStrictNormalCrossingsBoundary D`. The components and the number of them
  are exactly the family supplied by that definition. `kummerComponents` and
  `kummerIndices` only lift the existing finite family to the site universe.
- Complement: `(tameBoundaryOpen D).toScheme`, with its actual open inclusion.
- The two finite-rank lisse modules: `L L'`, and the two
  `IsLisseCoefficientModule` hypotheses. The existing lisse definition includes
  finite freeness locally; no extra rank or nonzero assumption is imposed.
- The two strict-local Kummer-tame hypotheses are exactly
  `IsStrictLocalKummerTameModule p ... D (tameBoundaryOpen D).ι L` and the same
  for `L'`. This uses the recorded compatible prime-to-p tower definition.
- An actual morphism: `(f : L ⟶ L')`, retained in every puncture square.
- Partition of J: `Jo Ji : Finset (Fin hD.2.2.choose)`, `Disjoint Jo Ji`, and
  `Ji.Nonempty`; J is their union. The lifted family uses that same union.

Conclusions, clause by clause:

- The conclusion gives a family `models : I → ChartPair ... L L' f` and the
  actual `Presieve.ofArrows` pro-etale covering condition on its boundary maps.
  `I` is in the scheme universe and is allowed to be empty.
- `ChartPair.chart : TameRootExtensionChart ...` is the existing affine etale
  chart with branch equations and affine weakly etale refinement. Its actual
  boundary is `U ×_Y S_J`, not a freely chosen scheme over the stratum.
- `ChartPair.geometry : TameRootChartGeometry ...` supplies compatible root
  characters, the actual full root algebra tower with power transitions, the
  root-rotation action, its punctured pro-etale covering, and the invertible
  canonical torsor comparison. Both modules and both fields share this data.
- `boundary`, `boundary_over`, and `roots_zero` identify the boundary map into
  the full root tower by setting every named root to zero.
- `representation` and `representation'` use the published
  `PartialKummer.FiniteRepresentation`. Its representation is norm-continuous,
  finite-dimensional, and supplied with a finite basis; rank zero is permitted.
- `DeckSplit.equiv` is a continuous multiplicative equivalence from the native
  full deck group to the outer-times-inner group. The `outer` and `inner`
  equations specify its individual coordinates, fixing the reordering.
- Each of the four `FieldChart`s has a published `PartialKummer.Condensation`.
  Its coordinate and action equations on every profinite test object specify
  exactly `C(P,F tensor_E M)` in a finite basis, with the product norm topology.
- `FieldChart.data.root : LisseRootExtension` has `extension`, `lisse`, `linearization`,
  `restriction`, and `restriction_equivariant` give the lisse extension and its actual equivariant
  puncture identification. The linearization and its laws live on full
  profinite parameter schemes, not merely at individual group elements.
- `FieldChart.data.root.constant` is the point-pullback identification of that extension
  with its finite representation module. Restricting it to `boundary` gives
  the displayed boundary module. `puncture_normalization` fixes the resulting
  puncture identification by the canonical inverse-image composition maps,
  `data.root.restriction`, and `fromCondensedPullbackIso`; `extensionPunctureIso` names
  precisely this composite.
- `extendToClosure` is the actual `Mod.extendScalars` functor for the continuous
  field inclusion. The closure charts have as their INPUTS its actual images
  of `L` and `L'`. `MorphismData.scalars.scalar` and `scalar'` compare the ordinary tensor
  extensions with those closure charts; `ScalarCompatibility.scalar_puncture` and
  `scalar_puncture'` normalize these isomorphisms against the actual puncture
  identifications. `scalarPunctureIso` uses only `CondensedRing.pullIso` and
  ordinary extension of scalars. It involves no direct image.
- `MorphismData.finiteMap` and `closureMap` are `CoefficientMorphism`s. Their
  `extensionMap` and `puncture_map` give precisely the actual extensions of f
  and of its ordinary scalar extension. `equivariant` is an equation on the
  entire deck-parameter scheme. Pulling it back along any continuous profinite
  family gives the node's family-equivariance assertion.
- `uniqueE` and `uniqueOmega` assert the actual restriction bijection for lisse
  extensions after every weakly etale base change of the tower. They also
  explicitly give the unique extension of every puncture isomorphism. Applied
  to an identity puncture map this is the unique identity-restricting comparison
  of two supplied extensions. The bijection and pullback functoriality identify
  the actual restricted extension maps on further common refinements.
- The continuous E-linear equivariant map is `MorphismData.matrix`,
  `matrix_continuous`, and `matrix_equivariant`. `matrixE` and `matrixOmega` use
  the published `PartialKummer.HasMatrix` to fix the two condensed arrows by
  exactly this same E-matrix on every profinite section, with the specified
  coefficient inclusions. Each `CoefficientMorphism.constant_map` says that
  the extended geometric arrow is point pullback of that arrow. Its boundary
  arrow is therefore the specified point pullback. `scalars.scalar_map` identifies
  the two actual geometric extension arrows under ordinary scalar extension.
- `InnerAlgebra` and `SuccessiveAlgebra` use the existing
  `FullParameterRootAlgebra`, first on the inner list and then on the images of
  the remaining parameters in the inner algebra. `SuccessiveRoots.equiv` is an
  actual ring equivalence to the full root algebra, fixed on base coefficients
  and EVERY named inner and outer root. These equations fix power transitions
  and intertwine the rotations on the two disjoint lists; they are not an
  arbitrary isomorphism of abstract schemes.
- `FieldChart.resolved.model.full.productAction_eq` identifies the product-group action with the
  actual root action through the specified coordinate reordering.
- `DoubleNerve.diagram` is an actual bisimplicial scheme over the punctured
  base; its `coordinates` identify term (a,b) with the full parameter scheme
  for `G_o^a × G_i^b`. `faceG`, `faceH`, `degeneracyG`, `degeneracyH` specify
  all operators as scheme-map equations, including the action first faces.
  `diagonal` is a natural isomorphism to the actual full Cech nerve;
  `diagonal_coordinates` fixes it by the actual tuple-reordering and canonical
  root-nerve coordinate map, including degree zero.
- `Environment.bar` is the published `ProductBar`: its internal Hom terms,
  evaluation/restriction formulas, actions and operators are specified there.
  `onComplex` applies the entire diagram to one nonnegative equivariant
  injective resolution. `iteratedTotal` has differential
  `d_o + (-1)^a d_i + (-1)^(a+b) d_resolution` with finite diagonal sums.
- `Environment.full` is the normalized full condensed bar. `outer`, `inner`
  are the existing specified invariant adjunctions; `inflation` is equality
  of their exact left adjoints with the full trivial-action functor.
  All these structures are supplied in the theorem's CONCLUSION, with no
  abelianness, resolution, or bar assumptions added to the theorem input.
- `Environment.comparison` is the existing
  `ProductBarResolutionComparison` for every representation and nonnegative
  injective resolution. Its `augmentations` are fixed on each component by
  invariant inclusions and the bar-zero coprojections, with quasi-isomorphisms.
  Its `diagonalIso` and `iteratedIso` are fixed by the actual derived-unit
  equations. `Environment.iteratedInvariantIso` is the inverse iterated identification,
  pulled back to the actual boundary by `kummerPointPullBig`.
- `ProductBarResolutionComparison.comparison_eq` says precisely that the
  full-bar identification, actual augmented diagonal-to-successive comparison,
  and gamma compose to point pullback of `productBarDerivedComparison`. That
  comparison is the ordinary derived conjugate under the specified composite
  inflation adjunctions. Its units and counits are those of those adjunctions.
- `degreeZeroIso` is the canonical localization of `extendSingleIso`: it
  identifies the extended nonnegative single with the ordinary derived M[0].
  `Environment.iteratedInvariantIso` includes this transport in its target, rather than
  silently identifying two differently presented single complexes.
- `FieldChart.resolved.model.successive` supplies the coherent resolved double geometric
  descent. Its `columns.data.terms` and the final column-square conjunct of
  `SuccessiveColumnLaws` identify every double column with the
  actual full-root counit/evaluation term, on the same underlying resolution.
  Both legs are natural transformations of the entire bisimplicial complexes.
  The section-evaluation and bar-column-component conjuncts of
  `SuccessiveColumnLaws` fix the product bar identification on all profinite
  sections and its map to internal Hom and the underlying resolution. The first
  two conjuncts of `SuccessiveTotalLaws` fix finite-total transport on every summand. `diagonal_normalization` and `iterated_normalization`
  identify the derived totals through this actual coherent roof.
- `FieldChart.successiveAugmentation` is now the actual successive geometric
  augmentation: resolution comparison, `successive.totals.data.augmentation`,
  `successive.totals.data.iteratedComparison`, then `Environment.iteratedInvariantIso`.
  `sectionUnit_components` fixes the degree-(0,0) map by the actual section
  unit. The augmentation-component conjuncts of `SuccessiveTotalLaws` compose it
  with the canonical total summand.
  The column-composition and bar-column component laws use HEq to avoid expanding
  definitionally identical functor-category terms during elaboration; they still
  require the exact canonical component maps.
  `successive.totals.data.gamma` has the pulled-back diagonal total as source.
  The gamma-augmentation conjunct of `SuccessiveTotalLaws` equates it to the diagonal augmentation inverse followed
  by the successive geometric augmentation and normalized invariant comparison.
  The augmentation-comparison conjunct ties this geometric comparison to the specified
  formal augmented product bar. The final theta-equation conjunct explicitly states gamma composed
  with the full-bar identification equals pulled-back theta.
  The first conjunct of `ResolvedRootLaws` ties the diagonal geometric
  augmentation to the normalized FULL geometric chart comparison.
- `FieldChart.resolved.model.full.normalizedNerve` is the published `KummerNormalizedChart`, not a
  bare existence of a derived isomorphism. It retains the coherent nonnegative
  resolved geometric Cech descent, actual augmentation, compatible roof,
  parameterized full-root terms, and every canonical counit/evaluation column
  square. Its `puncture_normalization` binds it to the supplied extensions.
- `CoefficientMorphism.naturality` is `FieldNatural`, both derived squares for
  the actual direct-image map induced by f and the boundary matrix map: its first
  conjunct is full geometric descent, its second is the actual successive
  augmentation arrow.
  `Environment.naturality` includes the two totalization squares AND the
  augmentation-comparison square for every compatible resolution lift. Via
  the fixed geometric nerve coordinates these give the stated object and
  arrow naturality on the full and successive nerves.
- `FieldChart.resolved.model.full.refinement : NormalizedRefinement ...` retains actual normalized charts after EVERY boundary
  restriction, with comparison exactly the canonical derived pullback of the
  original comparison (including composition and invariant-pullback transport).
  the successive refinement conjunct of `FieldChart.resolved.laws` separately requires an actual
  resolved double-geometric model after every boundary restriction and fixes its
  successive augmentation arrow by canonical derived pullback. Together with
  uniqueness of lisse extension, these equations give the assertions on further
  common refinements, including identities/composites.
- Both fields use exactly the same chart, root data and two E-representations.
  Every comparison lives in the ordinary unbounded derived category. The
  canonical `kummerPointPullBig` localization transport handles the ordinary
  coefficient-category universe without equating site universes.

Dependency declarations used (the owner definition nodes are added to stmt_deps):

- `Sheaf.Topology.ContinuousMapCondensedRing` and upstream
  `Profinite.continuousMapRingObj`: the all-continuous ring.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `condensedRingObj`, `coefficientRing`, `upperStarFromPoint`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `Mod.extendScalars`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: ordinary module derived functors.
- Upstream `ModuleObject.Derived.BoundedConstructible`: the common geometric
  and coefficient setting (no new constructibility condition is imposed).
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary` and its component family.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `IsStrictLocalKummerTameModule`.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `Modules`.
- `Sheaf.CategoryTheory.CondensedProductActionInflation`: `Invariants`,
  `ProductInvariants`, `trivial`, `inflate`, and their exact adjunctions.
- `Sheaf.Paper.NormContinuousMonodromyData`: `NormContinuousRepresentations`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` and the
  ordinary Mathlib/upstream `DerivedCategory`, `InjectiveResolution` APIs.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: the small pro-etale site and covering.
- `Sheaf.Paper.FullParameterRootTower`: `FullParameterRootAlgebra`,
  `fullParameterRoot`, `fullParameterRootSection`, `ParameterRootDeckGroup`,
  `ParameterStratum`.
- `Sheaf.Paper.TameRootTowerExtension`: `TameRootExtensionChart`, its actual maps,
  and `TameRootChartGeometry` (owned by def-sfb-tame-root-chart-geometry).
- `Sheaf.Paper.ProfiniteCoefficientLinearization`: the actual parameter action,
  linearization, restriction, and deck-descent comparison APIs.
- `Sheaf.Paper.PartialKummerBoundaryUnitModel`: `FiniteRepresentation`,
  `Condensation`, `HasMatrix`, `IsTameRootEquivariantIso`. These are published
  coefficient-model interfaces, not a use of the parent theorem to prove its
  prerequisite. The owner definition node is explicitly cited. The parent
  already exports the shared coefficient definitions used here. Before stage 3
  proves that parent using this prerequisite, the maintainer must separate its
  shared definitions into a common module to avoid an import cycle. This
  delivery uses the published owner records and introduces no duplicate data.
- `Sheaf.CategoryTheory.CondensedProductBarComparison`: `ProductBar`,
  `ProductBarResolutionComparison`, actual augmentations and normalized theta.
- `Sheaf.Paper.KummerNormalizedChart`: `KummerNormalizedChart` and its normalized
  coherent descent, including actual augmentation and geometric column squares.
- `Sheaf.Paper.KummerNerveCoordinates`: canonical full nerve coordinate maps.
- `Sheaf.Paper.KummerChartGeometryMaps`: actual local-open maps and equalities.
- `Sheaf.Paper.KummerStratumGeometry`: `kummerComponents`, `kummerIndices`.
- `Sheaf.Paper.KummerCoefficientModels`: the existing `kummerCoefficientRing`.
- `Sheaf.Paper.KummerRefinement`: `kummerInvariantPullbackIso`; the existing
  derived upper-star composition comparison is used with it.
- Upstream `ModuleObject.ChangeOfCoefficients`: `CondensedRing.pullIso`.

The available recorded proof dependencies are imported for stage 3. The four
unstated proof prerequisites (integral reduction family, equivariant adic fibre
realization, root-tower profinite base change, compatible Kummer Cech tower) are
named in the proof docstring; no nonexistent module is imported. They are proof
prerequisites, not missing notions needed to TYPE this statement.

Edge cases checked before statement construction:

- Empty stratum: `I` can be empty; the covering condition is the actual site
  condition, not a nonempty-index assumption.
- Trivial outer group: `Jo` can be empty; function powers and unnormalized
  nerves still exist, including degree zero, with identity insertions retained.
- Rank zero: no positive-rank hypothesis; `Fin 0 → F`, its zero representation,
  ordinary scalar extension, and the zero-dimensional matrix remain present.
- Either module can have a different rank; matrices are rectangular linear maps.
- No omitted branch: J is exactly the disjoint union; roots run over ALL
  prime-to-p orders and their compatibility, not only ell-power roots.
- Arbitrary continuous profinite families: equivariance is a scheme-map equation
  on the entire parameter object, not a statement only about geometric points.
- Refinements include identity and composite boundary maps; no ad hoc chosen
  scalar/direct-image comparison is used.

Searches for an existing exact statement:

- `msearch.py N0 lem-sfb-kummer-partial-nerve-naturality leanfinder` with
  “Successive Kummer root nerves yield iterated derived invariants naturally for
  morphisms of tame lisse condensed modules”: eight generic condensed-module
  results (`Condensed.profiniteSolid`, `CondensedMod`, `LightCondMod`, their
  abelian/monoidal/Grothendieck instances and free objects); no exact statement.
- `msearch.py ... loogle '"Kummer", "Sheaf"'`: zero results.
- `msearch.py ... grep` with
  `(Kummer|tame).*(nerve|invariant|boundary)|(nerve|invariant|boundary).*(Kummer|tame)`:
  zero Mathlib matches.
- `rg` of the project and upstream `WeilConjectures` for partial nerves,
  successive roots and Kummer naturality: no exact statement; the related
  geometric and formal bar modules listed above were read and reused.
- The node ID search in upstream `WeilConjectures` found no existing declaration.
  The DAG owner-node search found the already landed root-geometry,
  finite-continuous-coefficient, and normalized-descent definition nodes. Their
  recorded signatures and source docstrings were read; those nodes are reused.

No statement correction or disputed mathematical assertion is introduced.
The new definition nodes below own the reusable coordinate and normalized chart specifications.
The item cites it and the already landed owner interfaces. No dependency-interface
repair or mathematical statement correction is made.
Independent statement review is performed by the maintainer, as specified in the
worker brief; no independent reader is claimed here.

## New nodes

`def-sfb-kummer-successive-descent` owns the resolved successive geometric
descent, its column squares, diagonal-total gamma, augmentation, and refinement.
Its module is `Sheaf.Paper.KummerSuccessiveDescent`; its principal declaration is
`AlgebraicGeometry.ProEtale.KummerPartialNerve.SuccessiveDescent`. The detailed
source, searches and clause mappings appear under “New nodes (repair addition)” below.

`def-sfb-kummer-partial-nerve-chart` defines the reusable chart specification used
by this theorem: each field's actual lisse extension, coherent resolved descent,
and exact boundary-refinement law over the supplied successive-root coordinate
and normalized full/product-bar data.
Its module is `Sheaf.Paper.KummerPartialNerveChart`; its principal declaration is
`AlgebraicGeometry.ProEtale.KummerPartialNerve.FieldChart`. Its source is the
item's extracted successive-root argument in direct-images proof paragraph (3).
It adds no existence theorem. The theorem supplies the chart data in its
conclusion. All six modules are checked individually against the published build.

Searches made before creating the node: LeanSearch and LeanFinder with
“A normalized successive Kummer root chart with double geometric nerve and
product bar comparison” each return eight unrelated generic nerve/Kummer
results; Loogle with `"Kummer", "nerve"` returns zero; Mathlib grep with
`DoubleNerve|SuccessiveRoots|NormalizedRefinement|KummerPartialNerve` returns
zero. The exact outputs are preserved in mathlib_searches. The same grep of
the DAG, upstream and project sources finds no Kummer-chart specification;
`tools/blueprint_refs.py search 'successive root'` returns zero. Existing
formal product bars and existing normalized FULL root charts are reused;
they do not define the specified successive-root geometric double nerve.

The module/declaration split changes no mathematical clause: the coordinate
module below owns `DeckSplit`, `SuccessiveRoots`, `DoubleNerve`, `Environment`
and their canonical helpers; the chart module owns `NormalizedRefinement`,
`FieldExtension`, `FieldChart` and their canonical helpers. The morphism and scalar-morphism modules below own the actual morphism/scalar
squares and geometric successive augmentation. The item module owns the
simultaneous covering theorem and its chart-pair specification.

The canonical helpers `successiveCoefficient`, `successiveInnerRoot` and
`successiveOuterRoot` name the actual base map and generators used by
`SuccessiveRoots`; they reduce repeated elaboration of nested quotient-ring
instances. `FieldExtension.coefficientModule` is the already supplied
condensation with its bundled coefficient ring in the declared type. It
changes no data. The morphism and bar interfaces use this exact action module.

`def-sfb-kummer-partial-nerve-coordinates` owns the root-algebra and actual
geometric double-nerve specification used by the chart definition. Module:
`Sheaf.Paper.KummerPartialNerveCoordinates`; principal declaration:
`AlgebraicGeometry.ProEtale.KummerPartialNerve.DoubleNerve`. It defines the real
root algebras and coordinate maps, and specifies ALL double-nerve operators
and the actual diagonal identification. Existing formal `ProductBar` data
have coefficients in a condensed module category; they do not define this
geometric bisimplicial scheme over the actual punctured base. The same source
and searches above cover this missing geometric notion; their complete outputs
are also in this node's mathlib_searches. The chart node cites this node.

The chart data factors the fixed-ring interfaces `LisseRootExtension` and
`ResolvedRootChart` from the concrete finite-field condensation. This avoids
repeated kernel expansion of the all-continuous ring. `FieldChart.data` supplies
the existing condensation and its actual lisse extension; `FieldChart.resolved`
is the normalized resolved chart over that exact ring and coefficient object.
`condensationForRing` and `FieldExtension.coefficientModule` have exactly the
already supplied condensation as their data. No existence assertion, hypothesis
or normalization equation is removed by this factorization.

The coordinate/environment module also owns `Environment`, `Environment.iteratedInvariantIso`
and `degreeZeroIso`: it contains the generic formal bar normalization used by
the concrete root-chart specification. This separates the reusable formal
comparison and geometric coordinate data from the coefficient-specific resolved
chart. The coordinate node cites the existing bar-resolution/point-pullback
interface and ordinary derived-category interface for these declarations.


`def-sfb-kummer-partial-nerve-morphism` owns the actual chart arrow
specification `CoefficientMorphism`, the full geometric derived naturality
square `FieldNatural`, the canonical `FieldChart.successiveAugmentation`,
`UniqueLisseExtensions`, and the actual ordinary scalar functor and puncture
comparison. Module: `Sheaf.Paper.KummerPartialNerveMorphism`. The equations
and maps are the same as in the clause mapping above; no existence theorem
or arbitrary comparison is introduced. Source: the same extracted direct-image
paragraph (3), extension and nerve naturality argument.

`def-sfb-kummer-partial-nerve-scalar-morphism` owns the paired-field
`MorphismData` specification. Module:
`Sheaf.Paper.KummerPartialNerveScalarMorphism`. It retains the actual two
extension maps, their uniqueness, exactly one continuous equivariant finite
E-matrix and both `HasMatrix` equations, the two actual ordinary scalar
isomorphisms, their exact puncture normalizations, and scalar-map naturality.
The theorem's `ChartPair.maps` supplies this data; it is never an extra theorem
hypothesis. This node separates the scalar-compatibility notion from the
single-field chart-arrow notion so that each source compiles within 60 seconds.
Source: the same extracted direct-image paragraph (3), common finite-coefficient
and algebraic-closure construction.

Searches before the two additional nodes: LeanSearch query “Natural morphisms
of resolved Kummer root charts and ordinary scalar extension with the same
finite continuous matrix over a finite field and its algebraic closure” gave
eight generic root-pairing, scalar-tower, intermediate-field and Kummer-field
results, with no resolved chart arrow or paired scalar specification. Loogle
`"Kummer", "matrix"` returned zero. Mathlib grep
`CoefficientMorphism|MorphismData|FieldNatural|UniqueLisseExtensions` returned
zero. The same project/upstream/DAG search found only unrelated
`TotalSiteMorphismData`, `ProjectionMorphismData`, and `NagataRawMorphismData`
substring matches. The blueprint search “Kummer morphism” found an unrelated
diagonal-integrals node. Exact search records are stored in each new node.
Existing finite-continuous condensations, matrix predicates and ordinary
scalar/inverse-image coherence are reused; none is copied privately.


`ScalarCompatibility` factors the ordinary scalar and puncture equations over
fixed bundled coefficient rings. `MorphismData.scalars` instantiates it with
the actual published E-to-Omega coefficient map and exactly the four supplied
extensions and restriction isomorphisms. Its five fields are the same two
scalar isomorphisms, two canonical puncture equations and arrow equation
listed above. This factorization reduces concrete-ring expansion without
adding a hypothesis or changing an isomorphism or normalization.


`extendCoefficients` has an explicit functor type over fixed published ring
bundles. `extendToClosure` specializes it to the prescribed E-to-Omega map;
its data is still exactly `Mod.extendScalars`. The fixed-ring type avoids
re-elaborating the coefficient-ring construction in each closure-chart input.


## Returned-delivery repair

The returned immutable head was c8242d44615e. The retained packet already had
partial edits to the successive descent; the first required dry run reported
that KummerSuccessiveDescent.lean had no owning node. This repair supplies that
node and completes its records, without restarting the original construction.
The current base item was read and compared: only lean and stmt_deps change.
The original theorem signature and mathematical statement are preserved.

H3: successiveTerms are replaced by ResolvedRootChart.model.successive, the coherent
resolved double geometric descent described clause by clause above. The actual
column squares in `SuccessiveColumnLaws`, geometric augmentation, gamma and theta
equations in `SuccessiveTotalLaws`, both conjuncts of `ResolvedRootLaws`, and
`FieldNatural`'s successive conjunct address every missing successive-geometric clause.
The obsolete Environment.gamma name is removed; iteratedInvariantIso names
only the iterated transport, while `SuccessiveDescent.totals.data.gamma` is the requested
map out of the diagonal total and is explicitly tied to the augmentation.

H2: the item now directly cites def-sfb-kummer-partial-nerve-coordinates, which
owns DeckSplit, SuccessiveRoots and Environment. It also cites the new resolved
successive-descent definition. The accepted mechanical product-bar dependency
is retained.

## New nodes (repair addition)

`def-sfb-kummer-successive-descent`, module `Sheaf.Paper.KummerSuccessiveDescent`,
principal declaration `AlgebraicGeometry.ProEtale.KummerPartialNerve.SuccessiveDescent`,
owns the reusable coherent successive geometric descent specification, all
canonical double-resolution/totalization helpers, and its augmentation and
refinement law. The source is the same extracted successive-root argument of
direct-image proof (3). It supplies no existence theorem and contains no sorry.
Searches before completing this node: LeanSearch for resolved successive
geometric Kummer double nerves and canonical column/augmentation comparisons
returned eight generic augmented-Cech-nerve results; Loogle with Kummer, nerve
returned zero; Mathlib grep for SuccessiveDescent, doubleGeometricMap,
doubleResolution and diagonalTotalFunctor returned zero. Project/upstream and
DAG searches found no exact definition (only unrelated frame substring
matches); blueprint_refs.py search successive root returned zero. The exact
msearch records are preserved in the node. Existing full normalized charts,
parameterized terms and product-bar constructions are reused.

The coordinate node now calls its iterated-total identification
Environment.iteratedInvariantIso. The chart node cites successive descent
and specifies both geometric augmentations; the morphism node now specifies
both geometric naturality squares. These remain new definition nodes of this
packet, not changes to already landed dependency interfaces.

The totalization specification is factored as `SuccessiveTotals` over the exact
resolved geometric diagram and base complex. `SuccessiveDescent.totals` supplies
that specification; the surrounding column roof normalizations and actual section
unit equation bind it to the geometric diagram. `SuccessiveTotals.data` supplies the actual comparison and augmentation maps;
`SuccessiveTotalLaws` is the conjunction of every component, augmentation-comparison,
gamma-augmentation and theta equation. `SuccessiveColumns.data` supplies the actual
coherent roof and term maps; `SuccessiveColumnLaws` retains its two column quasi-isomorphism
conditions, composition and bar evaluation normalizations, and the exact column squares.
The coordinate-to-base equation is retained in the data since the canonical term
transport uses it. These data/law factors retain all requested normalizations. `TotalRoofNormalized` states the localized coherent-roof equation
with the total functor explicit. Component HEq equations compare the prescribed
canonical maps of definitionally equal types and do not introduce new choices.

The canonical helpers `homPullComplex` and `homPullExtendIso` name the published
termwise internal-Hom/point-pullback functor and its ordinary extension-by-zero
comparison. Transparent instance inference is confined to these helpers and
`pullComplexIso`; the specifications use their exact result types. No new
structural assumption is added to the environment or geometric input.

The chart specification also factors into `ResolvedFullRootChart` (the original
full geometric chart with its actual product action, coordinate nerve, puncture
normalization and full refinement), `ResolvedRootData` (that full chart and the
successive descent on exactly its resolutions), and `ResolvedRootLaws` (the equality
with full descent and successive refinement). `ResolvedRootChart.model` and `.laws`
retain both factors. `Environment.productGroth` explicitly stores the existing
Grothendieck property needed to instantiate the full normalized chart, avoiding
inference between propositionally equal abelian structures. The theorem supplies
this property as part of its environment conclusion.

All six repaired modules passed the server per-file compilation. The final dry
run passed preflight and compilation (dry-run commit a71be5d13d9). All node
signatures match their files verbatim, no Lean line exceeds 100 characters,
and the main theorem is the only declaration containing `sorry`. The final
report references above were then aligned with the compiled data/law factors.

## Second reading by N0

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
