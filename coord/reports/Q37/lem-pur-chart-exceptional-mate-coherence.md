## Worker report

The item is stated by `WeilConjectures.PurityFiniteSetting.ChartComparisons.chart_exceptional_mate_coherence`
in `Sheaf.Paper.ChartExceptionalMateCoherence`. The supporting new definition node
`def-pur-general-chart-comparisons` owns the general smooth-target constructions in
`Sheaf.Paper.GeneralChartComparisons`. There is no change to the item's statement.
All theorem proofs in this delivery are `sorry`; definitions have actual data.

Hypotheses and clauses, matched with the node:

- The field, distinct prime, finite extension E, coefficient quotient and positive
  level are exactly `P : PurityFiniteSetting`. No `P.extension = ⊥`, divisibility
  of the ramification index, auxiliary adjoint or orientation is assumed.
- Affine finite-type V is `(V : Scheme.{u}) [IsAffine V]`, its structure map `aV`,
  `[LocallyOfFiniteType aV] [QuasiCompact aV]`. Affine finite-type U with etale
  coordinates is `C : Chart V d`: `C.X` is affine and `C.coord` is etale to
  `AffineSpace (ULift.{u} (Fin d)) V`. `C.proj` is literally the coordinate
  composite with standard projection. `Chart.smooth` gives pure dimension d;
  finite type follows from the etale coordinate map and the projection, while
  separatedness and quasi-compactness follow from affineness. Thus h is not a
  new unspecified morphism or an extra assumption. `d : ℕ` includes zero.
- `standard V d` is the standard projection chart, `coordinate C` is the node's u.
  Charts retain genuine schemes, and all coefficient categories are the existing
  derived categories on the small pro-etale sites with ModuleCat.{u+1} P.Coefficient.
- `composition P B.proj aV e.hom` is literally
  `ProEtale.standingExceptionalComposition P e.hom B.proj (P.chartCoefficientUnit V)`
  with the displayed k-structures supplied internally. It uses the standing
  Hom equivalences, the actual origin compositor and its counit. In `ExceptionalMate`,
  `IsIso` concerns this exact arrow. Its conjugate characterization is not replaced
  by existence of an unrelated isomorphism: it is the actual definition in the
  recorded pur9 dependency, whose body transposes alpha followed by the counit.
- The next three conjuncts of `ExceptionalMate` say that K=Rh!A is bounded
  constructible, K is bounded below of etale origin, and Ru!K is bounded below
  of etale origin. They assert these facts, rather than requiring them as inputs.
  `omega` is the recorded finite exceptional functor evaluated at the coefficient
  unit; `supportOmega` is its actual compact-support image.
- `rho` is the canonical etale identification, transported through the published
  comparison unit. `epsilon` is inverse normalized etale locality with those same
  comparison units. The last equation of `ExceptionalMate` says c followed by rho
  is precisely epsilon (with `omegaCongr` inserting h=Pu). Consequently epsilon
  has the prescribed counit; there is no arbitrary comparison map hypothesis.
- `sectionObject` is `Dnc.sourceSection` for first projection and diagonal,
  and `normalSection` is `Dnc.normalSection` for the actual extended-Rees normal cone
  with its actual augmentation section. `alpha` reuses `chartDiagonalAlpha`, which
  is the inverse smooth counit-mate base-change map pulled along the diagonal.
- `sourceOrdinary` factors through W_X times_X U. `sourceLift` is the actual
  `(1,e)` map. Its counit-normalized etale restriction followed by inverse smooth
  section base change defines `source`, hence `q`. This is the global formula for
  restriction to the canonical Cartesian-centre neighbourhood and its pasted
  comparison, not a square falsely claiming that the whole inverse diagonal is
  the diagonal of U. The construction never uses an orientation.
- `deformation` is `Scheme.IdealSheafData.deformationSpaceMap` for the actual
  self-product map and diagonal ideals. `normalMap` is its zero-fibre pullback
  lift. `normalGeometry` states the actual normal square is Cartesian and its
  zero sections agree. `r` is inverse section base change for this square. Its
  degree-one map is [f] -> [e*f], the differential. No arbitrary normal frame
  or arbitrary normal-bundle isomorphism is supplied.
- `delta` selects from the unique normalized `Dnc.existsUnique_dncInvariance`.
  `integration` reuses `ChartFactors.beta`, defined independently by zero-section
  integration in the canonical conormal relative-Spec model. The ordinary/pro-etale
  comparison is explicit; `tateComparison` includes the canonical Tate constraint.
- In `ThreeEquations`, the first equation is q followed by pullback(alpha_P) =
  alpha_h followed by epsilon. The second is delta_h followed by r = q followed
  by pullback(delta_P). The third is r followed by pullback(beta_P) and the
  canonical Tate constraint = beta_h. These are equalities of isomorphisms, hence
  of their specified homs, rather than mere statements that the objects are isomorphic.
- `Identity` gives epsilon_1, q_1 and r_1 equal to identity after the canonical
  `ProEtale.leftDerivedUpperStarId` constraints. `Composition` gives all three
  binary pasting equations, displaying `leftDerivedUpperStarComp`. Applying them
  twice to three maps is exactly their associativity equation; no associativity
  datum is supplied by the caller. `Map.comp` is literal scheme composition.
- Further affine source-open restrictions are chart maps. For an affine open V'
  in V, a chart over V' is a chart over V by the etale map A^d_V' -> A^d_V.
  Its source and projection are the same schemes and composites, so comparisons
  with the original chart are covered by the same `Map` equations. The standard
  target-open restriction is another such chart. Iterating gives successive open
  restrictions and composable etale coordinate changes with the stated constraints.
- `Conclusion` gives the clauses first for every coordinate map to the standard
  chart, then for all composable maps between chart sources; identity clauses
  hold for every chart. The latter form supplies the further-chart comparisons
  required by the final paragraph of the node.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, `Coefficient`, `Ring`.
- `Sheaf.Paper.StandingExceptionalComposition`: `standingExceptionalComposition`,
  `standingExceptionalHomEquiv`, including the full definition and domain.
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`: `originCompactSupport`,
  `originCompositionAmbient`, `originComposition`, their actual comparison transport.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`: `ConstructibleOriginComparison`,
  `constructible_proEtale_origin`, including the intrinsic/origin equality.
- `Sheaf.Paper.FixedEtaleOriginDerivedCategory`: `FixedEtaleOriginDerivedCategory`
  and its forgetful functor; the actual domain assertion uses its underlying
  `DerivedCategory.plusEtaleOrigin` predicate, with no retained arbitrary witness.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the public finite
  `sfFiniteExceptionalAt` interface, which remains exposed with the recorded System.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`: `sectionInvariantFinite` and its
  intrinsic construction; the canonically compared fixed-coefficient realization
  used by `Dnc.sourceSection` is the published `sectionInvariant` interface.
- `Sheaf.Paper.PurityNormalProjection`: `purityNormalProjection` and
  `purityNormalProjection_eq`; the retraction-based normal projection is the same one.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`: `comparedDiagonalBaseChange` and
  `diagonalComparedRestriction`, used by the published `chartDiagonalAlpha`.
- `Sheaf.Paper.PurityDncInvariance`: `sourceComparison`, `normalComparison`,
  `pullComparison`, `existsUnique_dncInvariance`.
- `Sheaf.Paper.VectorBundlePurity`: `VectorBundlePurityConclusion`, `vectorBundlePurity`;
  integration is expressed through the actual published `ChartFactors.beta`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` publicly retains the fixed
  finite twists; the actual positive finite twist here is `diagonalTwistEtale`,
  compared using `vectorIntegrationBaseCoefficientPullback`.
- `Sheaf.Paper.DerivedPullbackTensorHom` supplies the intrinsic operations. Its finite
  pullback is transported to the fixed-scalar realization by the published
  `ProEtale.upperStar(...).leftDerivedFunctor`, with the existing Dnc comparisons.
- Mathlib: `AffineSpace`, `SmoothOfRelativeDimension`, `Etale`,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` (the separated clause of the
  recorded proper-morphism node). `Adjunction.comp` and `conjugateEquiv` are the
  composite-bijection/conjugate definitions underlying the standing comparison.
- Additional landed construction interfaces cited in stmt_deps:
  `def-pur-diagonal-dnc-chart-data` owns `chartDiagonalAlpha` and
  `chartSectionEtaleRestriction` and is cited by the new construction nodes.
  `def-pur-chart-affine-comparison-data` owns the landed `ChartFactors` source,
  normal and integration definitions, including `normalBundleComparison` and `beta`.
  The item cites this definition node; it does not cite the affine-factor theorem
  for those definitions. `def-pur-chart-coefficient-adjoint-data` owns
  `chartCoefficientUnit_constructible`, `chartCoefficientUnit` and
  `chartEtaleIdentification`, cited by the general-comparison definition node.
- Proof dependencies with recorded modules are imported as in the node. The
  generic mate-pasting and etale base-change leaves use the Mathlib/upstream APIs
  already publicly imported by the corresponding foundational modules.

Edge cases checked: empty U and empty V are allowed; no Nonempty hypothesis occurs.
The chart type includes d=0; its smoothness proof uses 0+d=d and all normal maps
retain empty degree-one lists. Arbitrary ramified E and levels n=1 and higher remain
included: there is no E=Q_l assumption, no rank or coefficient divisibility assumption.
Identity charts and repeated identity maps are covered by `Map.id` and `Identity`.
Non-injective etale coordinate maps use the two-square construction, avoiding the
incorrect global Cartesian-diagonal assertion. All universes and binders are explicit.

Searches: msearch LeanFinder on the item's full concept returned only etale geometry,
not this coherence theorem. Loogle on `CategoryTheory.conjugateEquiv,
CategoryTheory.Adjunction.comp` returned the generic adjunction-mate API; it does not
state the geometric three-equation result. Mathlib grep `chart.*coherence|exceptional.*composition`
returned no match. `rg` on upstream WeilConjectures and Sheaf found the existing
chart/DNC construction helpers but no item declaration or matching combined statement.
The new definition's separate LeanSearch, LeanFinder, Mathlib grep, source/project grep
and blueprint/DAG searches are recorded in its `mathlib_searches`.

Validation: both files compile cleanly through scompile.py, individually and in dependency
order in its private overlay. There are no compiler errors or warnings. No library build
or direct git command was run. The prescribed dry run and delivery results follow below.

## Second reading by Q37

This is a separate worker rereading, not an independent-agent endorsement; the dispatch
brief forbids starting other agents. The maintainer's independent delivery review follows.
I reopened the node and both sandbox modules. I checked the coefficient domain, affine
chart hypotheses, exact c definition, the three domain conjuncts, epsilon=rho c, all
three displayed equations, the actual normal cone, normalized delta, integration beta,
and identity/composition constraints against the node. During construction the general
source comparison initially shadowed its target projection g; that was fixed by naming
the intermediate projection g₀. A reserved identifier `over` was replaced by `over_eq`,
and the structure-map congruence uses the actual equality-induced `omegaCongr`.
The chart's local-finite-type instance was made explicit so it introduces no new
hypothesis. These were elaboration corrections; no mathematical clause changed.

The source and normal maps contain no orientation input. N and t quantify normalized
presentations, rather than postulate an isomorphism or an orientation. The third equation
retains its Tate constraint. The source-open and target-open cases are chart maps as
explained above. The actual normal map is the zero fibre of the actual Rees map and
not a chosen isomorphism. Every postponed typing theorem is named, documented with
its proof, and stated among the new definition node's construction assertions.

## New nodes

`def-pur-general-chart-comparisons` defines the general smooth-target two-square section
comparison, actual differential normal comparison, standing composition/rho/epsilon,
and affine chart/map packaging with its induced geometric typing facts. Source:
current orientation-charts proof Steps 1--4 and composition-coherence Step 1.
The existing `ChartDncVectorFactors` only supplies an affine-space target, which cannot
express composition between successive chart sources. Same-base section restriction
also does not give the required different-base chart comparison. Searches found no
existing general construction. This node reuses every available canonical primitive,
including the recorded diagonal data. The named `affine_specialization` theorem
identifies all seven relevant constructions with the already landed specialization.
All new geometric obligations are named theorems with proof docstrings; all new data
are explicit pullback, Rees, counit-locality or comparison constructions.


`def-pur-chart-affine-comparison-data` gives definition ownership to the already
landed `ChartFactors.selfMap`, `sourceLift`, `sourceOrdinary`, `source`,
`deformation`, `normalMap`, `normal`, `normalBundleComparison` and `beta`, with
their named geometric typing assertions. Its primary declaration is `beta` in
`Sheaf.Paper.ChartDncVectorFactors`; `existing: true` introduces no duplicate
module or data. The statement spells out the two-square counit comparison,
actual Rees/zero-fibre normal map and inverse integration transpose, without
assuming the equations of the theorem that formerly owned these helpers.
The source is the current orientation-charts proof Steps 1--4. The DAG/blueprint
and project searches located the landed declarations but no definition owner;
Mathlib searches returned etale-geometry and unrelated bundle results. This is
the definition record explicitly requested by return F1, also used by F3.

`def-pur-chart-coefficient-adjoint-data` owns the already landed coefficient-unit
constructibility assertion, the resulting bounded constructible object, and the
counit-preserving etale exceptional/pullback identification in
`Sheaf.Paper.DiagonalDncChartNormalization`, recorded with `existing: true`.
The first clause is exactly `chartCoefficientUnit_constructible`; the unit is
`chartCoefficientUnit`; Noetherian schemes, etale/separated/compactifiable map,
bounded-below ordinary K and normalization N are exactly the binders of
`chartEtaleIdentification`. Its composite retains the inverse derived unit,
normalized adjunction comparison, exact-pullback comparison and inverse site
pullback comparison. It assumes no orientation and includes arbitrary finite
ramified coefficients. The source is the current chart proof Step 3 and the
adjunction normalization used there. The same required searches found only
these existing project declarations, with no definition-node owner. This
repairs F2 without reproducing the data.

## Returned delivery repair

I compared the retained delivery (returned immutable head 4af079ce7cd0) with
current main by reading the current node and modules. The item's only changed
fields are `lean` and the permitted additions to `stmt_deps`. The mathematical
statement and all previously accepted clauses remain identical.

1. F1: removed `lem-pur-chart-dnc-vector-factors` and the directly added landed
   `def-pur-diagonal-dnc-chart-data` from the item's added statement dependencies.
   The item now cites the new definition owner
   `def-pur-chart-affine-comparison-data` for integration and its canonical model.
   The already landed diagonal-data node remains a dependency of the new
   definition nodes that actually use it; it is not presented as a new node.
2. F2: `delta` now literally evaluates
   `Dnc.existsUnique_dncInvariance ... .exists.choose`, using its recorded
   dependency. There is no reference to `chartDiagonalDelta` in either delivery
   module. The other two formerly uncited helpers have the new existing-definition
   owner `def-pur-chart-coefficient-adjoint-data`, which is explicitly cited in
   `def-pur-general-chart-comparisons` and in its statement.
3. F3: the new named theorem `ChartComparisons.affine_specialization` asserts
   equality, in order, of `selfMap`, `sourceLift`, `deformation`, `normalMap`,
   `sourceOrdinary`, `source` and `normal` with the existing `ChartFactors`
   constructions at the affine projection. Thus q and r have one identified
   specialization. The new definition node states all seven equalities, lists
   the declaration, and cites their affine definition owner. Its docstring gives
   the complete unfolding/proof-irrelevance argument; the postponed proof is
   `sorry`, as required for this stage. The smoothness instance is derived
   internally from the actual affine-space theorem and adds no assumption.

Repair rereading by Q37: checked every new owner against the full landed
signatures and docstrings, and the general specialization against both modules.
Empty schemes, d=0, ramified E, identity maps and arbitrary normalized N remain
included. There is no new scalar restriction or orientation input. The main
coherence theorem is unchanged; the only new theorem is the exact-specialization
identification requested by F3. No other worker was started.
