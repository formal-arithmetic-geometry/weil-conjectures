## Worker report

Stage 2 statement of `lem-tw-lisse-rational-realization`, with one named theorem
`WeilConjectures.LisseRealization.lisse_rational_realization`, whose proof is `sorry`.
The theorem docstring contains all eleven original proof steps, with their dependency names.
Definitions and comparison structures contain actual data specifications and no sorry.
The item statement is unchanged. Its stmt_deps gains the seven definition nodes supplied here
and two existing recorded nodes used in the statement.

Hypotheses and clause correspondence:

- The finite-field algebraic closure is the existing `FiniteFieldDatum D`; `l` has
  `[Fact l.Prime]`, and `hl : l ≠ D.p`. `Base` packages `Scheme.Over (Spec D.k)` and
  locally-finite-type plus quasi-compact structure map. It has no separatedness instance.
  `baseInvertible` derives residue-field invertibility from these inputs, by mapping
  the nonzero characteristic-prime cast from the finite field into the residue field.
- A finite coefficient field is quantified by `A : Type u`, `Field A`, `Algebra ℚ_[l] A`,
  `FiniteDimensional ℚ_[l] A`. Allowing arbitrary such models is equivalent to choosing
  their images in the fixed algebraic closure; the algebraic-closure part uses its actual
  finite subfields and the recorded Shrink coefficient models.
- The actual completed coefficient ring is `completedIntegralCommRingSheafUnrestricted`.
  `At.completion_residues` fixes its comparison with the continuous integral sheaf by every
  recorded limit projection. `At.localization` and `localization_unit` identify the actual
  SHEAF localization with `rationalCoefficientSheaf`. This never uses a sectionwise
  bounded-denominator definition in place of the sheaf localization.
- Ordinary module sheaves are `pbcModules` / existing `SheafOfModules`; ordinary tensor is
  the existing monoidal tensor. `At.image` uses the existing `IsFiniteLocallyFree`, allowing
  rank zero and varying finite local rank. The new predicate `IsRationalLisse` spells out
  a pro-etale cover, a rank `r : ℕ` on each chart, the integral free module on `ULift (Fin r)`,
  its single complex in degree zero, and an isomorphism only AFTER raw rationalization.
  `rationalLisseHeartProperty` intersects this with `sfRationalHeartProperty`.
- `At.J` has exactly the recorded raw category as source. `At.integral` fixes it naturally
  on integral representatives as `pbcDerivedExtend` along completion then localization.
  `At.fractions` sends scalar-first `a ⊗ f` to the field scalar times the localized arrow;
  this is the recorded Hom-first `f ⊗ a` formula under `sfRationalHomCoordinates`.
  `At.degree_zero`, `fully_faithful`, and `image` assert degree-zero concentration, Hom
  bijectivity on precisely the lisse heart, and exactly the ordinary finite locally free
  essential image. They express an equivalence onto that full subcategory without selecting
  an arbitrary equivalence or an integral lisse lattice.
- `TensorAt.unit` and `tensor` use the recorded completed unit and tensor.
  Its naturality, associativity, symmetry and left/right-unit equations use the recorded
  completed comparisons and the ordinary monoidal constraints. `TensorNormalized.models`
  requires the comparisons to come from EVERY pair of good integral representatives:
  `TensorModel.quotients` fixes the finite quotient-coordinate map, `shifted` fixes its
  zero shifted coordinate, `scalar_sections` sends c tensor (x tensor y) to
  (1 tensor x) tensor (c tensor y), and `HomologyTensor.sections` fixes the induced pairing
  on local cocycles. This rules out an arbitrary tensor comparison and fixes basis and
  pure-tensor normalization. The unit is then fixed by the left-unit equation as well.
- `Along` quantifies arbitrary `f : X.scheme ⟶ Y.scheme`, not morphisms over k. Its
  comparison is with the actual `ordinaryPull`, defined as existing exact site inverse
  image followed by ordinary scalar extension along the continuous coefficient map.
  `PullNormalized.sections` fixes pulled-back generators by the actual ordinary integral
  adjunction unit and tensor-with-one map. Its `derived_normalized` fixes the derived
  balancing comparison on complexes. `normalized` inserts precisely the inverse of
  `ordinaryIntegralCompletionComparison`, not an arbitrary comparison. `heart` identifies
  its degree-zero map with `Along.comparison`, with the degree-zero identification required
  to induce identity on H0. Thus a pulled-back basis vector is the same basis vector.
- `Composition.sections` and `Identity.sections` fix ordinary comparisons by tensor-unit
  sections and the canonical base-change projections; their compatibility fields are the
  actual diagrams with `pullbackTensorRationalComposition`. `PullTensor` fixes the ordinary
  tensor-pullback comparison on pure generators and its square with the recorded completed
  tensor-pullback comparison. These contain the identity and repeated-map cases.
- `FieldChange.normalized` fixes the coefficient map pointwise. `FieldNormalized` fixes
  its comparison by `completedScalarComparison` and the derived counits and canonical
  balanced associators. `FieldComposition`, `Mixed`, and `FieldTensor` give the composition,
  pullback, and tensor diagrams with pure-section formulas. Repeated fields and identity
  embeddings are permitted by the same quantifiers. All exactness witnesses occur in the
  CONCLUSION, as structure fields, not as extra hypotheses of the theorem.
- `CommonStage` uses `GeneralAlgebraicallyClosedCoefficients.stageSystem` and the existing
  `StageSystem.Morphism.functor` on the actual quotient of representatives. Its transitions
  are ordinary `pbcExtend` along the finite-field coefficient maps; `stages` fixes each
  stage realization. Its Hom-bijection and image assertions are on the intersection of
  `sfCommonStageHeartProperty` with the existing `IsCommonStageLisse`.
  `CommonNormalized.transitions` fixes the descent comparisons on lisse objects to the
  same finite-stage comparisons. Therefore finite diagrams of tensor, pullback, and point
  maps are checked at a common finite stage, with no replacement common-stage category.
- `point`, `sections`, and `fibre` use Spec k, ordinary evaluation with constant E-scalar
  restriction, and H0 of the RECORDED `pointRationalFibre`, respectively. `PointAt.degree_zero`
  additionally states that the recorded derived fibre is concentrated in degree zero.
  Its natural comparison, composed with `Along.comparison` for any x : s → X, is the requested
  fibre/ordinary-pullback comparison. `PointNormalized.sections` is exactly c tensor m maps
  to c(1 tensor m); its derived equation uses termwise exact functors and the specified
  scalar counit. `square` ties this to `pointRationalNormalization`, including the carrier
  size descent. Tensor and unit agree by the tensor normalization on point free models.
- `ordinaryPointTransport` is a REAL construction: ordinary module unit followed by
  restriction along the distinguished base-change coprojection. `transport` is H0 after
  rationalization of the existing `pointTransport` (restriction then the specified kappa),
  for EVERY point automorphism. `TransportAt.target_normalization` inserts only the recorded
  raw pullback object equality (HEq with identity). `square` explicitly intertwines the
  two arrows on each section. Naturality and the pullback composition equation permit
  iteration; applying the same square successively proves the assertion for every iterate,
  including the identity/zeroth iterate. Finite-field compatibility and the common-stage
  descent give the corresponding algebraic-closure assertion.

Dependency declarations used (modules are under `Sheaf` unless otherwise specified):
`NumberTheory.Padics.CoefficientExtensionFinite` (Padic coefficient integers/uniformizer),
`Paper.CompletedIntegralConstantMapOfUniverses` (actual completed coefficient limit),
`Paper.SfRationalizationKaroubi` (sfRationalConstructibleCategory, localization,
coefficient equivalence), `Paper.SfConstructibleHeart` (sfRationalHeartProperty,
sfCommonStageHeartProperty), `Paper.DerivedPullbackTensorHom` (rationalDerivedPullback,
rationalDerivedTensor, rationalTensorScalarComparison, rationalPullbackScalarComparison),
`Paper.DerivedPullbackTensorIso` (pullbackTensorRationalUnit, associator, braiding,
unitors, composition, canonicalRationalPullbackTensor),
`Paper.GeneralAlgebraicallyClosedCoefficients` (stageSystem, Stage, transition),
`Paper.CommonStageLocallyFree` (IsCommonStageLisse), `Paper.FiniteCoefficientPoint`
(pointRationalFibre, pointRationalNormalization), `SixFunctors.FrobeniusPointTransport`
(the recorded restriction/kappa normalization), `Paper.PointAutomorphismTransportScalarExtension`
(pointTransport for arbitrary automorphisms), `Paper.ContinuousRationalDerivedRealization`
(ContinuousRational.modulePull, moduleUnit, derivedPull, IsNormalizedPullCounit),
`AlgebraicGeometry.ContinuousCoefficientCompletion` (completion and sheaf-localization
presentations), `AlgebraicGeometry.ContinuousCoefficientPullback`
(continuousCoefficientPullback), `Paper.CompletedCoefficientPresentationTransport`
(purCoefficientIso), `SixFunctors.ConstructibleTensorCompletion`
(constructibleTensorTotal, section, integralCompletedTensorComparison),
`Paper.OrdinaryCompletedIntegralPullback` (ordinaryIntegralModulePull,
adjunction, derived pull and its normalized completion comparison),
`Paper.FiniteFreeCompletedScalarComparison` (completedCoefficientMap,
completedScalarComparison and its tensor sections), `Paper.BoundedConstructibleTower`
(pbcExtend, pbcDerivedExtend, pbcComplexCounit, pbcReductionNormalization), and
`WeilConjectures.CategoryTheory.StageSystem.Functor` (Morphism.functor).
The original proof-dependency imports are retained.

Edge cases checked: empty X and empty covers; the zero object and rank zero; disconnected
bases with different finite ranks; nonseparated finite-type schemes; arbitrary non-k-linear
scheme maps; identity and repeated pullbacks; identity and repeated coefficient embeddings;
positive-exponent convention n+1 for completed coefficients; exact size lift for the point
fibre; no choice of global lisse lattice; arbitrary point automorphisms and all successive
iterates. The small pro-etale site retains distinct object and morphism universes.

Searches: msearch LeanFinder queried the full lisse realization sentence (8 unrelated condensed
category hits); Loogle queried SheafOfModules and Equivalence (3 pushforward equivalences);
LeanSearch queried locally finite free rationalized-heart realization (8 ordinary free-pullback
hits); Mathlib grep for lisse/rationalization/ellAdicSheaf found only ElladicCohomology.
Repository rg and DAG/blueprint searches found the existing common-stage lisse predicate,
Pbc realization, ordinary operations and point fibre interfaces, but no finite raw lisse predicate
or normalized interface with these operations. Actual search outputs are recorded in every new
node's mathlib_searches. No STATEMENT-DISPUTED flag and no source correction is needed.

## Second reading by Q12

The dispatcher explicitly prohibits starting other agents, so this is a separate author rereading,
not a claim of an independent second worker. Read the node against all seven files. Repaired:
ordinary pullback tensor arrow direction; explicit local-cocycle tensor normalization; missing
point/scalar comparison normalization; the point transport target object equality; coefficient
composition and common-stage representative compatibility; degree-zero comparison must induce
identity on H0; implicit site/coefficient universe arguments; and file-local instance visibility.
The maintainer's independent delivery review remains the requested independent review.

## New nodes

`def-real-rational-lisse-heart` defines finite-stage local rational freeness and its intersection
with the existing heart, source BS 6.8.3/6.8.14. It is the finite-stage counterpart of the existing
common-stage predicate, not a duplicate of it.

`def-real-lisse-realization-data` packages the normalized coefficient presentation, raw realization,
ordinary lisse image, tensor/pullback/scalar diagrams, point transport, and common-stage quotient
interface. Source BS 6.8.2/6.8.14/6.8.15 and the item's explicit normalization. It defines witness
data, makes no existence assertion, and reuses all recorded operations.

`def-real-lisse-tensor-normalization` packages the universal-counit representative and local-cocycle
normalization for tensor, with specified completion coordinates, source BS 6.8.15 and the recorded
constructible tensor completion map. `def-real-lisse-pullback-normalization` packages the ordinary
adjunction-unit and derived completion-map normalization of pullback, with the same source.
`def-real-lisse-field-normalization` packages normalization by the recorded finite-free scalar
completion comparison, source BS 6.8.2/6.8.15. `def-real-lisse-point-normalization` packages the
sections/localization map and its termwise derived descent, source BS 6.8.2/6.8.14.
For each, the searches above found no existing declaration giving this exact interface. These
separate modules keep every per-file compile under the fixed timeout and contain only definitions.

The additional new node `def-real-point-automorphism-transport-construction`
is definition ownership for the existing restriction, derived lift, kappa and
transport, with Deligne (1.1.3)/(1.1.7) as context and the published agent-written
completed-coefficient construction as its explicit source. LeanSearch returned
eight generic restriction results; Loogle and Mathlib grep returned zero.
Repository searches found the four exact definitions in the published module,
and the DAG search found only the scalar-extension theorem as their former
owner. Hence this new node uses `existing: true` and adds no Lean module.

## Returned delivery repair

The immutable returned head was `11eb25685607`. The retained packet was first
dry-run against the current live branch; commit `478c8fb5725` passed preflight
and every per-file compile. The required repair retains all seven Lean modules
unchanged; the delivery wrapper rebases the repaired packet on current main.

H2: `def-real-point-automorphism-transport-construction` now owns the four
existing declarations in `Sheaf.Paper.PointAutomorphismTransportScalarExtension`:
`WeilConjectures.pointAutomorphismRestrictionModules`,
`WeilConjectures.pointAutomorphismRestrictionDerived`,
`WeilConjectures.pointTransportKappa`, and `WeilConjectures.pointTransport`.
Its `existing: true` record points to the unchanged published module. Its statement
is exactly the integral module restriction, its localized termwise derived lift,
the specified inverse-image/pullback comparison, and their composite; no
scalar-extension conclusion is asserted. Read their complete definitions and
docstrings, including the prime-unit input and the canonical coefficient unlift.
Both `def-real-lisse-realization-data` and the item cite this definition node in
place of `lem-weil-point-automorphism-transport-scalar-extension`.

The new node cites `lem-weil-point-automorphism-restriction-natural`, whose
`AlgebraicGeometry.ProEtale.point_automorphism_restriction_natural` supplies
the transformation with its sectionwise component equations, and
`def-weil-inverse-image-pullback-comparison`, whose
`AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived` supplies
the actual map on an arbitrary derived object. Their recorded signatures and
docstrings were read. No conclusion about scalar extension is needed to define
these four maps. Identity automorphisms and arbitrary derived objects are included.

`def-real-lisse-pullback-normalization` now explicitly cites
`def-sf-ordinary-integral-pullback-construction` for
`ordinaryIntegralModulePull`, `ordinaryIntegralModuleAdjunction`, and
`ordinaryIntegralPullComplex`; their definitions in
`Sheaf.Paper.OrdinaryCompletedIntegralPullback` were read. The original
`lem-tw-ordinary-completed-integral-pullback` remains a dependency for the
specified ordinary-to-completed derived comparison. The unused
`lem-weil-pbc-continuous-coefficients-immersion-restriction` is removed from
`def-real-lisse-realization-data` (its citation is removed from that new node's
statement too); it remains a proof dependency of the item where it is used.
The item's mathematical statement and proof are unchanged.

Advisory, `Identity.raw`: its restriction to the lisse heart is fixed by the
other fields, despite being stored as an isomorphism on the whole raw category.
`Identity.sections` fixes `ordinary` uniquely on ordinary pullback generators
(the adjunction unit, then linearity and sheafification). `PullNormalized.sections`,
`derived_normalized`, `integralCompletion_normalized`, `normalized`, and `heart`
fix `ai.comparison` on lisse integral representatives. Raw rationalization has
those same objects, and its arrows are localized fractions. For each lisse K,
`Identity.compatibility` therefore fixes `a.sheaf.map (raw.hom.app K)`. Both
K and its identity pullback are lisse by `Along.preserves`, so the injective
part of `At.fully_faithful` fixes `raw.hom.app K` itself. The theorem only
asserts identity compatibility on lisse objects; any freedom on other raw
objects changes none of its clauses. Thus no free scalar rescaling of the
identity comparison survives on the subcategory stated by the item.

Repair second reading: checked these dependency substitutions against the
node statements and the actual four definition bodies. The associator, braiding,
unitors and composition comparisons still use their recorded unique
constructions, as accepted by the return. No definition, hypothesis, universe
binder, target statement or proof is altered by this repair.
